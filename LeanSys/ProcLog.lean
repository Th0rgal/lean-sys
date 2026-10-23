/-
  LeanSys.ProcLog: Bounded `pread` Process Log Chunk & Tail Reader
  (`0 import Lean`, `0 sorryAx`)
  - Reads bounded `[offset, offset + maxBytes)` chunks of live subprocess logs via `preadByteArray`
  - Cuts non-EOF chunks back to the last newline (`'\n'`) and strips incomplete trailing UTF-8 codepoint sequences
  - Every returned `(startOff, nextOff, fileLen)` window is gated by
    `LeanSys.Spec.verifyLogWindow` (`leansys_verify_log_window`)
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash

namespace LeanSys.ProcLog

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash

/-- Maximum bytes returned by a single `readLogChunk` call (256 KiB). -/
@[inline] def maxLogChunkBytes : Nat := 262144

/-- Default tail size for `readLogTail` (64 KiB). -/
@[inline] def defaultLogTailBytes : Nat := 65536

/-- Result of a bounded positional log chunk read. -/
structure LogChunk where
  data       : String
  startOff   : UInt64
  nextOff    : UInt64
  reachedEof : Bool
  deriving Repr, DecidableEq

/-- Find the length of a prefix ending at the last newline `'\n'` (`10`), or `len` if none exists. -/
def cutAtLastNewline (ba : ByteArray) (len : Nat) : Nat := Id.run do
  let mut i := len
  while i > 0 do
    i := i - 1
    if byteAt ba i == 10 then
      return i + 1
  return len

/-- Trim any incomplete trailing multi-byte UTF-8 sequence at the end of `ba[0..len)`. -/
def trimIncompleteUtf8Suffix (ba : ByteArray) (len : Nat) : Nat := Id.run do
  if len == 0 then return 0
  let mut back : Nat := 1
  while back ≤ 3 && back ≤ len do
    let idx := len - back
    let b := byteAt ba idx
    if (b &&& 0x80) == 0 then return len
    else if (b &&& 0xC0) == 0x80 then back := back + 1
    else
      let needed : Nat := if (b &&& 0xE0) == 0xC0 then 2 else if (b &&& 0xF0) == 0xE0 then 3 else 4
      return if back < needed then idx else len
  return len

/-- Read a bounded log chunk from `logPath` starting at `offset` (up to `maxBytes ≤ 256 KiB`),
    gated by `leansys_verify_log_window`. -/
def readLogChunk (logPath : String) (offset : UInt64) (maxBytes : Nat := 65536) (terminal : Bool := false)
    : IO (SysResult LogChunk) := do
  let cappedMax := Nat.min (Nat.max maxBytes 4) maxLogChunkBytes
  withFd logPath 0 fun fd => do
    let raw ← preadByteArray fd offset (cappedMax + 1)
    let reachedEof := raw.size ≤ cappedMax
    let rawLen := Nat.min raw.size cappedMax
    let lineCut := if !reachedEof then cutAtLastNewline raw rawLen else rawLen
    let validLen := if !terminal || !reachedEof then trimIncompleteUtf8Suffix raw lineCut else lineCut
    let startOff := offset
    let nextOff := startOff + validLen.toUInt64
    let fileFloor := startOff + raw.size.toUInt64
    if verifyLogWindow startOff nextOff fileFloor cappedMax.toUInt64 != 1 then
      return .error .einval
    let slice : ByteSlice := { ba := raw, off := 0, len := validLen }
    return .ok {
      data := slice.toStringLossy, startOff := startOff, nextOff := nextOff,
      reachedEof := reachedEof && validLen == raw.size
    }

/-- Read up to the last `maxTailBytes` of `logPath` when the total size is bounded by `maxFileBytes`. -/
def readLogTail (logPath : String) (maxTailBytes : Nat := defaultLogTailBytes) : IO (SysResult String) := do
  let cap := Nat.min maxTailBytes maxLogChunkBytes
  withFd logPath 0 fun fd => do
    let raw ← preadByteArray fd 0 (cap * 4)
    let start := if raw.size > cap then raw.size - cap else 0
    let len := raw.size - start
    if verifyLogWindow start.toUInt64 raw.size.toUInt64 raw.size.toUInt64 cap.toUInt64 != 1 then
      return .error .einval
    let slice : ByteSlice := { ba := raw, off := start, len := len }
    return .ok slice.toStringLossy

/-- Stateless Sans-IO scanner for `/proc/<pid>/stat` lines past the last `')'` of `(comm)`,
    gated by `leansys_verify_proc_stat_fields`. Returns `(commSlice, fieldsAfterComm)`. -/
def scanProcStatFields? (line : ByteSlice) (minFieldsAfterComm : Nat := 3) : Option (ByteSlice × Nat) := Id.run do
  let ba := line.ba
  let start := line.off
  let stop := Nat.min (line.off + line.len) ba.size
  let mut openIdx : Option Nat := none
  let mut closeIdx : Option Nat := none
  for i in [start:stop] do
    let b := byteAt ba i
    if b == 40 && openIdx.isNone then openIdx := some i
    if b == 41 then closeIdx := some i
  let some oIdx := openIdx | return none
  let some cIdx := closeIdx | return none
  let mut fields : Nat := 0
  let mut inTok := false
  for j in [cIdx + 1 : stop] do
    let b := byteAt ba j
    if b == 32 || b == 9 || b == 10 || b == 13 then inTok := false
    else if !inTok then inTok := true; fields := fields + 1
  let relOpen := (oIdx - start).toUInt64
  let relClose := (cIdx - start).toUInt64
  let totalLen := (stop - start).toUInt64
  if verifyProcStatFields relOpen relClose totalLen minFieldsAfterComm.toUInt64 fields.toUInt64 != 1 then
    return none
  let commSlice : ByteSlice := { ba := ba, off := oIdx + 1, len := cIdx - (oIdx + 1) }
  return some (commSlice, fields)

/-- Zero-copy parsed `/proc/<pid>/stat` record extracted via `procStatTailStep` and gated by `verifyProcStatFields`. -/
structure ProcStatRecord where
  commSlice       : ByteSlice
  stateByte       : UInt8
  startTicks      : UInt64
  fieldsAfterComm : Nat

/-- Parse an unsigned `UInt64` from ASCII digits in `s : ByteSlice`. -/
def parseSliceUInt64? (s : ByteSlice) : Option UInt64 := Id.run do
  let ba := s.ba
  let stop := Nat.min (s.off + s.len) ba.size
  if s.off ≥ stop then return none
  let mut acc : UInt64 := 0
  for i in [s.off : stop] do
    let b := byteAt ba i
    if b < 48 || b > 57 then return none
    acc := acc * 10 + (b - 48).toUInt64
  return some acc

/-- Verified Slice-IO parser for `/proc/<pid>/stat` lines:
    1. Locates the first `'('` and the last `')'` of `(comm)` (handling spaces and nested parentheses).
    2. Advances into the post-`comm` tail via `procStatTailStep` (`TotalSliceParserSpec`).
    3. Tokenizes whitespace-separated fields past `')'` and extracts `state` (field 3, index 0 after `comm`)
       and `starttime` (field 22, index 19 after `comm`).
    4. Gates the extraction via `leansys_verify_proc_stat_fields` (`minFieldsAfterComm >= 20`). -/
def parseProcStatRecord? (line : ByteSlice) : Option ProcStatRecord := Id.run do
  let ba := line.ba
  let start := line.off
  let stop := Nat.min (line.off + line.len) ba.size
  let totalNat := stop - start
  let mut openIdx : Option Nat := none
  let mut closeIdx : Option Nat := none
  for i in [start:stop] do
    let b := byteAt ba i
    if b == 40 && openIdx.isNone then openIdx := some i
    if b == 41 then closeIdx := some i
  let some oIdx := openIdx | return none
  let some cIdx := closeIdx | return none
  let relOpen := oIdx - start
  let relClose := cIdx - start
  let initBounds : SliceBounds := { off := start, len := totalNat, cap := ba.size }
  let some (_, tailBounds) := procStatTailStep relClose initBounds | return none
  let mut fields : Nat := 0
  let mut inTok := false
  let mut tokStart : Nat := tailBounds.off
  let mut stateByte? : Option UInt8 := none
  let mut startTicksSlice? : Option ByteSlice := none
  let tailStop := tailBounds.off + tailBounds.len
  for j in [tailBounds.off : tailStop] do
    let b := byteAt ba j
    let isWs := b == 32 || b == 9 || b == 10 || b == 13
    if isWs then
      if inTok then
        if fields == 1 then
          stateByte? := some (byteAt ba tokStart)
        else if fields == 20 then
          startTicksSlice? := some { ba := ba, off := tokStart, len := j - tokStart }
        inTok := false
    else if !inTok then
      inTok := true
      tokStart := j
      fields := fields + 1
  if inTok then
    if fields == 1 then
      stateByte? := some (byteAt ba tokStart)
    else if fields == 20 then
      startTicksSlice? := some { ba := ba, off := tokStart, len := tailStop - tokStart }
  if verifyProcStatFields relOpen.toUInt64 relClose.toUInt64 totalNat.toUInt64 20 fields.toUInt64 != 1 then
    return none
  let some stByte := stateByte? | return none
  let some ticksSlice := startTicksSlice? | return none
  let some ticks := parseSliceUInt64? ticksSlice | return none
  let commSlice : ByteSlice := { ba := ba, off := oIdx + 1, len := cIdx - (oIdx + 1) }
  return some {
    commSlice := commSlice,
    stateByte := stByte,
    startTicks := ticks,
    fieldsAfterComm := fields
  }

end LeanSys.ProcLog
