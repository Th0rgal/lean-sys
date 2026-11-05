/-
  LeanSys.Sse: W3C Server-Sent Events (SSE) Encoder & Stateful Multi-Chunk Event Accumulator
  (`0 import Lean`, `0 sorryAx`)
  - Serializes `event:` / `id:` / `retry:` / multi-line `data:` SSE frames gated by `LeanSys.Spec.verifySseEventEncode`
    (strictly rejecting CR/LF header injection in `event` / `id` fields)
  - Provides stateful `SseEventStream` incremental parser over arbitrary TCP/HTTP chunk boundaries:
    - W3C SSE §9.2.5 / §9.2.6 line endings (`\r\n`, `\n`, and standalone `\r`, including cross-chunk `\r` + `\n`)
    - Initial UTF-8 BOM (`0xEF 0xBB 0xBF`) stripping on the first chunk
    - Lossy UTF-8 replacement (`U+FFFD`) on invalid byte sequences instead of dropping field lines
    - Strict `retry:` digits-only parsing (after stripping at most one leading space) and persistent `lastRetryMs?`
    - Bounded pending event memory (`carry + pendingBytes <= maxCarryCap`) across chunks
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

/-- Decode `ba` as UTF-8 per Unicode §3.9 D93b / WHATWG UTF-8 decoder (maximal valid subpart replacement
    with `U+FFFD` `0xEF 0xBF 0xBD`). -/
def decodeUtf8Lossy (ba : ByteArray) : String :=
  match String.fromUTF8? ba with
  | some s => s
  | none => Id.run do
    let mut out := ByteArray.emptyWithCapacity (ba.size * 3)
    let mut i : Nat := 0
    while i < ba.size do
      let b0 := ba.get! i
      if b0 < 0x80 then
        out := out.push b0
        i := i + 1
      else if 0xC2 ≤ b0 && b0 ≤ 0xDF then
        if i + 1 < ba.size && ((ba.get! (i + 1)) &&& 0xC0) == 0x80 then
          out := out.push b0 |>.push (ba.get! (i + 1))
          i := i + 2
        else
          out := out.push 0xEF |>.push 0xBF |>.push 0xBD
          i := i + 1
      else if 0xE0 ≤ b0 && b0 ≤ 0xEF then
        let validB1 :=
          i + 1 < ba.size &&
          let b1 := ba.get! (i + 1)
          (b1 &&& 0xC0) == 0x80 && !(b0 == 0xE0 && b1 < 0xA0) && !(b0 == 0xED && b1 ≥ 0xA0)
        if !validB1 then
          out := out.push 0xEF |>.push 0xBF |>.push 0xBD
          i := i + 1
        else if i + 2 < ba.size && ((ba.get! (i + 2)) &&& 0xC0) == 0x80 then
          out := out.push b0 |>.push (ba.get! (i + 1)) |>.push (ba.get! (i + 2))
          i := i + 3
        else
          -- Maximal valid prefix of length 2 (`b0`, `b1`) replaced by a single U+FFFD
          out := out.push 0xEF |>.push 0xBF |>.push 0xBD
          i := i + 2
      else if 0xF0 ≤ b0 && b0 ≤ 0xF4 then
        let validB1 :=
          i + 1 < ba.size &&
          let b1 := ba.get! (i + 1)
          (b1 &&& 0xC0) == 0x80 && !(b0 == 0xF0 && b1 < 0x90) && !(b0 == 0xF4 && b1 ≥ 0x90)
        if !validB1 then
          out := out.push 0xEF |>.push 0xBF |>.push 0xBD
          i := i + 1
        else if !(i + 2 < ba.size && ((ba.get! (i + 2)) &&& 0xC0) == 0x80) then
          -- Maximal valid prefix of length 2 (`b0`, `b1`)
          out := out.push 0xEF |>.push 0xBF |>.push 0xBD
          i := i + 2
        else if i + 3 < ba.size && ((ba.get! (i + 3)) &&& 0xC0) == 0x80 then
          out := out.push b0 |>.push (ba.get! (i + 1)) |>.push (ba.get! (i + 2)) |>.push (ba.get! (i + 3))
          i := i + 4
        else
          -- Maximal valid prefix of length 3 (`b0`, `b1`, `b2`)
          out := out.push 0xEF |>.push 0xBF |>.push 0xBD
          i := i + 3
      else
        out := out.push 0xEF |>.push 0xBF |>.push 0xBD
        i := i + 1
    return String.fromUTF8? out |>.getD ""

/-- Stateful incremental W3C SSE stream parser handling arbitrary chunk splits and multi-line `data:` concatenation. -/
structure SseEventStream where
  carry        : ByteArray := ByteArray.empty
  curEvent     : String := ""
  lastEventId  : Option String := none
  lastRetryMs? : Option Nat := none
  dataLines    : Array String := #[]
  pendingBytes : Nat := 0
  sawFirstByte : Bool := false
  skipNextLf   : Bool := false
  maxCarryCap  : Nat := 4194304

namespace SseEventStream

def init (maxCarryCap : Nat := 4194304) : SseEventStream :=
  { maxCarryCap := maxCarryCap }

/-- W3C SSE §9.2.6 `retry`: digits `0..9` ONLY (no extra leading/trailing whitespace). -/
private def parseDigitsOnlyNat? (s : String) : Option Nat := Id.run do
  let b := s.toUTF8
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
  if st.carry.size + chunkBytes.size + st.pendingBytes > st.maxCarryCap then
    return none
  let rawBuf := if st.carry.isEmpty then chunkBytes else st.carry ++ chunkBytes
  if rawBuf.isEmpty then
    return some (st, #[])
  let mut startIdx : Nat := 0
  let mut skipLf := st.skipNextLf
  if skipLf then
    skipLf := false
    if rawBuf.get! 0 == 10 then
      startIdx := 1
  let mut sawFirst := st.sawFirstByte
  if !sawFirst then
    if rawBuf.size - startIdx < 3 then
      -- Could still be a partial UTF-8 BOM (`0xEF` or `0xEF 0xBB`) at stream start
      let b0 := rawBuf.get! startIdx
      if b0 == 0xEF && (rawBuf.size - startIdx == 1 || rawBuf.get! (startIdx + 1) == 0xBB) then
        return some ({ st with carry := rawBuf.extract startIdx rawBuf.size, skipNextLf := false }, #[])
      sawFirst := true
    else
      sawFirst := true
      if rawBuf.get! startIdx == 0xEF && rawBuf.get! (startIdx + 1) == 0xBB && rawBuf.get! (startIdx + 2) == 0xBF then
        startIdx := startIdx + 3
  let mut curEv := st.curEvent
  let mut lastId := st.lastEventId
  let mut lastRetry := st.lastRetryMs?
  let mut dLines := st.dataLines
  let mut pendBytes := st.pendingBytes
  let mut emitted : Array SseEvent := #[]
  let mut lineStart : Nat := startIdx
  let mut i : Nat := startIdx
  while i < rawBuf.size do
    let b := rawBuf.get! i
    if b == 10 || b == 13 then -- '\n' or '\r'
      let lineEnd := i
      let nextPos :=
        if b == 13 then
          if i + 1 < rawBuf.size && rawBuf.get! (i + 1) == 10 then i + 2 else i + 1
        else i + 1
      if b == 13 && i + 1 == rawBuf.size then
        skipLf := true
      if lineEnd == lineStart then
        -- Blank line dispatches event iff at least one `data:` field was accumulated (W3C SSE §9.2.6)
        if !dLines.isEmpty then
          let evName := if curEv.isEmpty then "message" else curEv
          let joined := String.intercalate "\n" dLines.toList
          emitted := emitted.push {
            event := evName
            id? := lastId
            retryMs? := lastRetry
            data := joined
          }
        curEv := ""
        dLines := #[]
        pendBytes := 0
      else if rawBuf.get! lineStart == 58 then
        -- Comment / keepalive line (`:...`): ignore
        pure ()
      else
        let lineStr := decodeUtf8Lossy (rawBuf.extract lineStart lineEnd)
        match lineStr.splitOn ":" with
        | [] => pure ()
        | [fieldOnly] =>
          if fieldOnly == "data" then
            if pendBytes + 1 > st.maxCarryCap then
              return none
            dLines := dLines.push ""
            pendBytes := pendBytes + 1
          else if fieldOnly == "event" then
            curEv := ""
          else if fieldOnly == "id" then
            lastId := some ""
        | field :: rest =>
          let rawVal := String.intercalate ":" rest
          let val := if rawVal.startsWith " " then (rawVal.drop 1).toString else rawVal
          if field == "data" then
            let addBytes := val.utf8ByteSize + 1
            if pendBytes + addBytes > st.maxCarryCap then
              return none
            dLines := dLines.push val
            pendBytes := pendBytes + addBytes
          else if field == "event" then
            if val.utf8ByteSize > st.maxCarryCap then
              return none
            curEv := val
          else if field == "id" then
            if val.utf8ByteSize > st.maxCarryCap then
              return none
            -- W3C SSE §9.2.6: ignore `id` containing NULL
            if (val.splitOn "\x00").length == 1 then
              lastId := some val
          else if field == "retry" then
            if let some ms := parseDigitsOnlyNat? val then
              lastRetry := some ms
      lineStart := nextPos
      i := nextPos
    else
      i := i + 1
  let rem := if lineStart < rawBuf.size then rawBuf.extract lineStart rawBuf.size else ByteArray.empty
  if rem.size + pendBytes + curEv.utf8ByteSize > st.maxCarryCap then
    return none
  return some ({
    carry := rem
    curEvent := curEv
    lastEventId := lastId
    lastRetryMs? := lastRetry
    dataLines := dLines
    pendingBytes := pendBytes
    sawFirstByte := sawFirst
    skipNextLf := skipLf
    maxCarryCap := st.maxCarryCap
  }, emitted)

end SseEventStream

end LeanSys.Sse
