/-
  LeanSys.Sse: W3C Server-Sent Events (SSE) Encoder & Stateful Multi-Chunk Event Accumulator
  (`0 import Lean`, `0 sorryAx`)
  - Serializes `event:` / `id:` / `retry:` / multi-line `data:` SSE frames gated by `LeanSys.Spec.verifySseEventEncode`
    (strictly rejecting CR/LF header injection in `event` / `id` fields)
  - Provides stateful `SseEventStream` incremental parser over arbitrary TCP/HTTP chunk boundaries,
    accumulating multi-line `data:` payloads and dispatching completed events on empty-line (`\n\n` / `\r\n\r\n`) boundaries
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Codec

namespace LeanSys.Sse

open LeanSys.Spec
open LeanSys.Posix

/-- Decoded W3C Server-Sent Event message. -/
structure SseEvent where
  event   : String := "message"
  id?     : Option String := none
  retryMs?: Option Nat := none
  data    : String
  deriving Repr, DecidableEq, Inhabited

/-- `true` iff `s` contains no `\r` (`13`) or `\n` (`10`) bytes (preventing SSE field-injection). -/
def hasNoCrLf (s : String) : Bool := Id.run do
  let b := s.toUTF8
  for i in [0:b.size] do
    let c := b.get! i
    if c == 10 || c == 13 then return false
  return true

/-- Format a keepalive comment frame (`: keepalive\n\n`). -/
def formatSseKeepalive (comment : String := "keepalive") : ByteArray :=
  if hasNoCrLf comment then
    s!": {comment}\n\n".toUTF8
  else
    ": keepalive\n\n".toUTF8

/-- Encode an `SseEvent` into wire `ByteArray`, splitting multi-line `data` across `data: ...` lines
    and gating header CR/LF absence and total byte budget via `LeanSys.Spec.verifySseEventEncode`. -/
def formatSseEvent? (ev : SseEvent) (maxChunkBytes : Nat := 4194304) : Option ByteArray := Id.run do
  let evClean := hasNoCrLf ev.event
  let idClean := match ev.id? with | none => true | some idStr => hasNoCrLf idStr
  let noCrLfFlag : UInt8 := if evClean && idClean then 1 else 0
  let normalizedData := (ev.data.replace "\r\n" "\n").replace "\r" "\n"
  let rawLines := normalizedData.splitOn "\n"
  let lines := if rawLines.isEmpty then [""] else rawLines
  let mut out := ""
  if !ev.event.isEmpty && ev.event != "message" then
    out := out ++ s!"event: {ev.event}\n"
  if let some idStr := ev.id? then
    out := out ++ s!"id: {idStr}\n"
  if let some rMs := ev.retryMs? then
    out := out ++ s!"retry: {rMs}\n"
  for ln in lines do
    out := out ++ s!"data: {ln}\n"
  out := out ++ "\n"
  let wire := out.toUTF8
  if verifySseEventEncode noCrLfFlag lines.length.toUInt32 wire.size.toUInt64 maxChunkBytes.toUInt64 == 1 then
    return some wire
  else
    return none

/-- Stateful incremental W3C SSE stream parser handling arbitrary chunk splits and multi-line `data:` concatenation. -/
structure SseEventStream where
  carry       : ByteArray := ByteArray.empty
  curEvent    : String := ""
  lastEventId : Option String := none
  curRetryMs? : Option Nat := none
  dataLines   : Array String := #[]
  maxCarryCap : Nat := 4194304

namespace SseEventStream

def init (maxCarryCap : Nat := 4194304) : SseEventStream :=
  { maxCarryCap := maxCarryCap }

private def parseAsciiNat? (s : String) : Option Nat := Id.run do
  let b := s.trimAscii.toString.toUTF8
  if b.isEmpty then return none
  let mut acc : Nat := 0
  for i in [0:b.size] do
    let c := b.get! i
    if 48 ≤ c && c ≤ 57 then
      acc := acc * 10 + (c - 48).toNat
    else
      return none
  return some acc

/-- Feed a raw `ByteSlice` chunk into `st`, returning `(updatedState, dispatchedEvents)` or `none` if buffer cap is exceeded. -/
def pushChunk? (st : SseEventStream) (chunk : ByteSlice) : Option (SseEventStream × Array SseEvent) := Id.run do
  let chunkBytes := chunk.toByteArray
  if st.carry.size + chunkBytes.size > st.maxCarryCap then
    return none
  let buf := if st.carry.isEmpty then chunkBytes else st.carry ++ chunkBytes
  let mut curEv := st.curEvent
  let mut lastId := st.lastEventId
  let mut curRetry := st.curRetryMs?
  let mut dLines := st.dataLines
  let mut emitted : Array SseEvent := #[]
  let mut lineStart : Nat := 0
  let mut i : Nat := 0
  while i < buf.size do
    if buf.get! i == 10 then -- '\n'
      let lineEnd := if i > lineStart && buf.get! (i - 1) == 13 then i - 1 else i
      if lineEnd == lineStart then
        -- Blank line dispatches event iff at least one `data:` field was accumulated (W3C SSE §9.2.6)
        if !dLines.isEmpty then
          let evName := if curEv.isEmpty then "message" else curEv
          let joined := String.intercalate "\n" dLines.toList
          emitted := emitted.push {
            event := evName
            id? := lastId
            retryMs? := curRetry
            data := joined
          }
        curEv := ""
        curRetry := none
        dLines := #[]
      else if buf.get! lineStart == 58 then
        -- Comment / keepalive line (`:...`): ignore
        pure ()
      else
        if let some lineStr := String.fromUTF8? (buf.extract lineStart lineEnd) then
          match lineStr.splitOn ":" with
          | [] => pure ()
          | [fieldOnly] =>
            if fieldOnly == "data" then
              dLines := dLines.push ""
            else if fieldOnly == "event" then
              curEv := ""
            else if fieldOnly == "id" then
              lastId := some ""
          | field :: rest =>
            let rawVal := String.intercalate ":" rest
            let val := if rawVal.startsWith " " then (rawVal.drop 1).toString else rawVal
            if field == "data" then
              dLines := dLines.push val
            else if field == "event" then
              curEv := val
            else if field == "id" then
              -- W3C SSE §9.2.6: ignore `id` containing NULL
              if (val.splitOn "\x00").length == 1 then
                lastId := some val
            else if field == "retry" then
              if let some ms := parseAsciiNat? val then
                curRetry := some ms
      lineStart := i + 1
    i := i + 1
  let rem := if lineStart < buf.size then buf.extract lineStart buf.size else ByteArray.empty
  return some ({
    carry := rem
    curEvent := curEv
    lastEventId := lastId
    curRetryMs? := curRetry
    dataLines := dLines
    maxCarryCap := st.maxCarryCap
  }, emitted)

end SseEventStream

end LeanSys.Sse
