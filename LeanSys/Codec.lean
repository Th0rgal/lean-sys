/-
  LeanSys.Codec: Zero-Copy JSON / JSONL Tape Parser & Binary Frame Indexer
  (`0 import Lean`, `0 sorryAx`)
  - Scans a borrowed `ByteSlice` in a single pass without `String.splitOn` allocations
  - Every extracted `(keyOff, keyLen, valOff, valLen)` span is gated by
    `LeanSys.Spec.verifyJsonlTape` (`leansys_verify_jsonl_tape`)
  - Provides O(1)-allocation field lookups (`lookupSlice?`, `lookupString?`, `lookupNat?`, `lookupBool?`)
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash

namespace LeanSys.Codec

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash (byteAt readWord64LE)

/-- Zero-copy JSON key-value tape entry pointing into a backing `ByteArray`. -/
structure JsonTapeEntry where
  keyOff   : Nat
  keyLen   : Nat
  valOff   : Nat
  valLen   : Nat
  isString : Bool
  deriving Repr, DecidableEq

/-- Zero-copy indexed view of a JSON object over a backing `ByteSlice`. -/
structure JsonTape where
  root    : ByteSlice
  entries : Array JsonTapeEntry

namespace JsonTape

/-- Advance index `i` past ASCII whitespace (`' '`, `'\t'`, `'\r'`, `'\n'`). -/
@[inline]
def skipWs (ba : ByteArray) (i limit : Nat) : Nat := Id.run do
  let mut p := i
  while p < limit do
    let c := byteAt ba p
    if c == 32 || c == 9 || c == 10 || c == 13 then
      p := p + 1
    else
      break
  return p

/-- Scan a quoted JSON string starting right after the opening `"` (`ba[start - 1] == '"'`),
    handling `\"` escapes. Returns the index of the closing `"`. -/
@[inline]
def scanQuotedString (ba : ByteArray) (start limit : Nat) : Option Nat := Id.run do
  let mut p := start
  while p < limit do
    let c := byteAt ba p
    if c == 92 then -- '\\'
      p := p + 2
    else if c == 34 then -- '"'
      return some p
    else
      p := p + 1
  return none

/-- Scan a non-quoted JSON scalar or nested object/array value starting at `start`.
    Returns `(valEnd, maxDepthReached)`. -/
def scanRawValue (ba : ByteArray) (start limit : Nat) : Nat × UInt32 := Id.run do
  let mut p := start
  let mut depth : UInt32 := 0
  let mut maxDepth : UInt32 := 1
  let mut inStr := false
  while p < limit do
    let c := byteAt ba p
    if inStr then
      if c == 92 then p := p + 2
      else if c == 34 then inStr := false; p := p + 1
      else p := p + 1
    else
      if c == 34 then
        inStr := true
        p := p + 1
      else if c == 123 || c == 91 then -- '{' or '['
        depth := depth + 1
        if depth > maxDepth then maxDepth := depth
        p := p + 1
      else if c == 125 || c == 93 then -- '}' or ']'
        if depth == 0 then break
        depth := depth - 1
        p := p + 1
      else if depth == 0 && (c == 44 || c == 32 || c == 9 || c == 10 || c == 13) then
        break
      else
        p := p + 1
  return (p, maxDepth)

/--
  Build a zero-copy `JsonTape` over `s : ByteSlice` in a single linear scan,
  verifying every `(keyOff, keyLen, valOff, valLen)` span through `LeanSys.Spec.verifyJsonlTape`.
-/
def indexJsonObject (s : ByteSlice) : JsonTape := Id.run do
  let ba := s.ba
  let cap := ba.size
  let limit := Nat.min (s.off + s.len) cap
  let mut entries : Array JsonTapeEntry := Array.mkEmpty 16
  let mut p := skipWs ba s.off limit
  if p < limit && byteAt ba p == 123 then -- '{'
    p := p + 1
  while p < limit do
    p := skipWs ba p limit
    if p ≥ limit then break
    let c := byteAt ba p
    if c == 125 then break -- '}'
    if c == 44 then -- ','
      p := skipWs ba (p + 1) limit
    if p ≥ limit || byteAt ba p != 34 then
      p := p + 1
    else
      let keyStart := p + 1
      match scanQuotedString ba keyStart limit with
      | none => break
      | some keyEnd =>
        let keyLen := keyEnd - keyStart
        p := skipWs ba (keyEnd + 1) limit
        if p ≥ limit || byteAt ba p != 58 then -- ':'
          break
        p := skipWs ba (p + 1) limit
        if p ≥ limit then break
        if byteAt ba p == 34 then -- string value
          let valStart := p + 1
          match scanQuotedString ba valStart limit with
          | none => break
          | some valEnd =>
            let valLen := valEnd - valStart
            if verifyJsonlTape keyStart.toUInt64 keyLen.toUInt64 valStart.toUInt64 valLen.toUInt64 cap.toUInt64 1 == 1 then
              entries := entries.push {
                keyOff := keyStart, keyLen := keyLen,
                valOff := valStart, valLen := valLen, isString := true
              }
            p := valEnd + 1
        else
          let valStart := p
          let (valEnd, maxDepth) := scanRawValue ba valStart limit
          let valLen := valEnd - valStart
          if verifyJsonlTape keyStart.toUInt64 keyLen.toUInt64 valStart.toUInt64 valLen.toUInt64 cap.toUInt64 maxDepth == 1 then
            entries := entries.push {
              keyOff := keyStart, keyLen := keyLen,
              valOff := valStart, valLen := valLen, isString := false
            }
          p := valEnd
  return { root := s, entries := entries }

/-- Word-strided byte equality: 8 bytes per compare, then a byte tail. -/
def eqBytesFrom (ba : ByteArray) (off : Nat) (t : ByteArray) (i : Nat) : Bool :=
  if i + 8 ≤ t.size then
    readWord64LE ba (off + i) == readWord64LE t i && eqBytesFrom ba off t (i + 8)
  else if i < t.size then
    byteAt ba (off + i) == byteAt t i && eqBytesFrom ba off t (i + 1)
  else true
termination_by t.size - i

/-- Check if `[off, off + len)` in `ba` matches `targetBytes` byte-for-byte without allocation. -/
@[inline]
def sliceEqBytes (ba : ByteArray) (off len : Nat) (targetBytes : ByteArray) : Bool :=
  len == targetBytes.size && off + len ≤ ba.size && eqBytesFrom ba off targetBytes 0

/-- Find the tape entry for `key` (no allocation: `String.toUTF8` is a field projection). -/
@[inline]
def findEntry? (tape : JsonTape) (key : String) : Option JsonTapeEntry :=
  let kb := key.toUTF8
  let ba := tape.root.ba
  tape.entries.find? fun e => sliceEqBytes ba e.keyOff e.keyLen kb

/-- Lookup a field's raw `ByteSlice` value in `tape` by `key` without copying the backing buffer. -/
def lookupSlice? (tape : JsonTape) (key : String) : Option (ByteSlice × Bool) := Id.run do
  let keyBytes := key.toUTF8
  let ba := tape.root.ba
  for e in tape.entries do
    if sliceEqBytes ba e.keyOff e.keyLen keyBytes then
      return some ({ ba := ba, off := e.valOff, len := e.valLen }, e.isString)
  return none

/-- Lookup a string field in `tape` by `key`. -/
def lookupString? (tape : JsonTape) (key : String) : Option String := do
  let e ← findEntry? tape key
  let ba := tape.root.ba
  let stop := Nat.min (e.valOff + e.valLen) ba.size
  some (String.fromUTF8! (ba.extract e.valOff stop))

/-- Parse leading ASCII digits of `[i, stop)` into `acc`. -/
def parseDigits (ba : ByteArray) (i stop acc : Nat) (found : Bool) : Option Nat :=
  if i < stop then
    let b := byteAt ba i
    if 48 ≤ b && b ≤ 57 then parseDigits ba (i + 1) stop (acc * 10 + (b - 48).toNat) true
    else if found then some acc else none
  else if found then some acc else none
termination_by stop - i

/-- Lookup an unsigned `Nat` field in `tape` by `key` directly from ASCII digits in the slice. -/
def lookupNat? (tape : JsonTape) (key : String) : Option Nat := do
  let e ← findEntry? tape key
  if e.valLen == 0 then none
  let ba := tape.root.ba
  parseDigits ba e.valOff (Nat.min (e.valOff + e.valLen) ba.size) 0 false

/-- Lookup a boolean field (`true` / `false`) in `tape` by `key` without allocation. -/
def lookupBool? (tape : JsonTape) (key : String) : Option Bool := do
  let e ← findEntry? tape key
  let ba := tape.root.ba
  let b0 := byteAt ba e.valOff
  let b1 := byteAt ba (e.valOff + 1)
  if e.valLen == 4 && b0 == 116 && b1 == 114 then -- "tr..."
    some true
  else if e.valLen == 5 && b0 == 102 && b1 == 97 then -- "fa..."
    some false
  else
    none

/-- Split a multi-line JSONL `ByteSlice` into zero-copy line `ByteSlice` views without copying lines. -/
def splitJsonlLines (s : ByteSlice) : Array ByteSlice := Id.run do
  let ba := s.ba
  let limit := Nat.min (s.off + s.len) ba.size
  let mut out : Array ByteSlice := #[]
  let mut lineStart := s.off
  let mut i := s.off
  while i < limit do
    if byteAt ba i == 10 then -- '\n'
      let rawLen := i - lineStart
      let effLen := if rawLen > 0 && byteAt ba (lineStart + rawLen - 1) == 13 then rawLen - 1 else rawLen
      if effLen > 0 then
        if let some sub := ByteSlice.subSlice? (ByteSlice.ofByteArray ba) lineStart effLen then
          out := out.push sub
      lineStart := i + 1
    i := i + 1
  if lineStart < limit then
    let remLen := limit - lineStart
    if let some sub := ByteSlice.subSlice? (ByteSlice.ofByteArray ba) lineStart remLen then
      out := out.push sub
  return out

end JsonTape

/-- Zero-copy SSE field span `(fieldKind, valOff, valLen)` inside a borrowed `ByteSlice`.
    `fieldKind`: `1 = event`, `2 = data`, `3 = id`, `4 = retry`. -/
structure SseFieldSpan where
  fieldKind : UInt8
  valOff    : Nat
  valLen    : Nat
  deriving Repr, DecidableEq

/-- Incremental zero-copy SSE frame scanner (`leansys_sse_frame_scan`) over a borrowed `ByteSlice`:
    splits `event:` / `data:` / `id:` / `retry:` lines without cutting multi-byte UTF-8 sequences. -/
def scanSseFrames (s : ByteSlice) : Array SseFieldSpan × Nat := Id.run do
  let ba := s.ba
  let cap := ba.size
  let limit := Nat.min (s.off + s.len) cap
  let mut spans : Array SseFieldSpan := #[]
  let mut lineStart := s.off
  let mut i := s.off
  while i < limit do
    if byteAt ba i == 10 then
      let lineEnd := if i > lineStart && byteAt ba (i - 1) == 13 then i - 1 else i
      let lineLen := lineEnd - lineStart
      if lineLen > 0 then
        let mut colon := lineStart
        while colon < lineEnd && byteAt ba colon != 58 do
          colon := colon + 1
        if colon < lineEnd then
          let keyLen := colon - lineStart
          let b0 := byteAt ba lineStart
          let kind : UInt8 :=
            if keyLen == 5 && b0 == 101 then 1 -- "event"
            else if keyLen == 4 && b0 == 100 then 2 -- "data"
            else if keyLen == 2 && b0 == 105 then 3 -- "id"
            else if keyLen == 5 && b0 == 114 then 4 -- "retry"
            else 0
          let valStart := if colon + 1 < lineEnd && byteAt ba (colon + 1) == 32 then colon + 2 else colon + 1
          let valLen := if lineEnd ≥ valStart then lineEnd - valStart else 0
          let nextB := if i + 1 < limit then byteAt ba (i + 1) else 0
          let lastB := if valLen > 0 then byteAt ba (valStart + valLen - 1) else 0
          if valLen > 0 && verifySseFrameScan valStart.toUInt64 valLen.toUInt64 cap.toUInt64 kind nextB lastB == 1 then
            spans := spans.push { fieldKind := kind, valOff := valStart, valLen := valLen }
      lineStart := i + 1
    i := i + 1
  return (spans, lineStart)

/-- Zero-copy GFM pipe table row span `(rowOff, rowLen, colCount, isSeparator)`. -/
structure GfmPipeRowSpan where
  rowOff      : Nat
  rowLen      : Nat
  colCount    : UInt32
  isSeparator : Bool
  deriving Repr, DecidableEq

/-- Single-pass zero-copy GFM loose-pipe table scanner (`leansys_gfm_pipe_scan`):
    indexes pipe-delimited rows, respects escaped pipes `\|`, and validates column counts against the separator row. -/
def scanGfmPipeTable (s : ByteSlice) : Array GfmPipeRowSpan := Id.run do
  let ba := s.ba
  let cap := ba.size
  let limit := Nat.min (s.off + s.len) cap
  let mut rawRows : Array (Nat × Nat × UInt32 × Bool × UInt8) := #[]
  let mut sepCols : UInt32 := 0
  let mut lineStart := s.off
  let mut i := s.off
  while i ≤ limit do
    if i == limit || byteAt ba i == 10 then
      let lineEnd := if i > lineStart && byteAt ba (i - 1) == 13 then i - 1 else i
      let rowLen := lineEnd - lineStart
      if rowLen > 0 then
        let mut p := lineStart
        let mut pipes : UInt32 := 0
        let mut nonSep := false
        let mut esc : UInt8 := 0
        while p < lineEnd do
          let c := byteAt ba p
          if esc == 1 then
            esc := 0
          else if c == 92 then -- '\\'
            esc := 1
          else if c == 124 then -- '|'
            pipes := pipes + 1
          else if c != 45 && c != 58 && c != 32 && c != 9 then
            nonSep := true
          p := p + 1
        if pipes > 0 then
          let firstPipe := byteAt ba (JsonTape.skipWs ba lineStart lineEnd) == 124
          let lastPipe := lineEnd > lineStart && byteAt ba (lineEnd - 1) == 124
          let cols := pipes + 1 - (if firstPipe then 1 else 0) - (if lastPipe && pipes > 1 then 1 else 0)
          let isSep := !nonSep && cols > 0
          if isSep && sepCols == 0 then sepCols := cols
          rawRows := rawRows.push (lineStart, rowLen, cols, isSep, esc)
      lineStart := i + 1
    i := i + 1
  let mut out : Array GfmPipeRowSpan := #[]
  let targetCols := if sepCols > 0 then sepCols else (rawRows[0]?.map (·.2.2.1)).getD 0
  for (rOff, rLen, cols, isSep, esc) in rawRows do
    if verifyGfmPipeScan rOff.toUInt64 rLen.toUInt64 cap.toUInt64 cols targetCols esc == 1 then
      out := out.push { rowOff := rOff, rowLen := rLen, colCount := cols, isSeparator := isSep }
  return out

/-- Zero-copy rich tag (`<file>`, `<image>`, `<svg>`) span (`tagKind`: `1 = file`, `2 = image`, `3 = svg`). -/
structure RichTagSpan where
  tagKind : UInt8
  tagOff  : Nat
  tagLen  : Nat
  attrOff : Nat
  attrLen : Nat
  deriving Repr, DecidableEq

/-- Zero-copy `<file>`, `<image>`, `<svg>` tag scanner (`leansys_tag_scan`) over a borrowed `ByteSlice`. -/
def scanRichTags (s : ByteSlice) : Array RichTagSpan := Id.run do
  let ba := s.ba
  let cap := ba.size
  let limit := Nat.min (s.off + s.len) cap
  let mut out : Array RichTagSpan := #[]
  let mut i := s.off
  while i + 4 < limit do
    if byteAt ba i == 60 then -- '<'
      let b1 := byteAt ba (i + 1)
      let b2 := byteAt ba (i + 2)
      let b3 := byteAt ba (i + 3)
      let (kind, nameLen) : UInt8 × Nat :=
        if b1 == 102 && b2 == 105 && b3 == 108 && i + 5 < limit && byteAt ba (i + 4) == 101 then (1, 4) -- "file"
        else if b1 == 105 && b2 == 109 && b3 == 97 && i + 6 < limit && byteAt ba (i + 4) == 103 && byteAt ba (i + 5) == 101 then (2, 5) -- "image"
        else if b1 == 115 && b2 == 118 && b3 == 103 then (3, 3) -- "svg"
        else (0, 0)
      if kind != 0 then
        let attrStart := JsonTape.skipWs ba (i + 1 + nameLen) limit
        let mut closeIdx := attrStart
        while closeIdx < limit && byteAt ba closeIdx != 62 do -- '>'
          closeIdx := closeIdx + 1
        if closeIdx < limit then
          let tagLen := (closeIdx + 1) - i
          let attrLen := closeIdx - attrStart
          if verifyTagScan i.toUInt64 tagLen.toUInt64 attrStart.toUInt64 attrLen.toUInt64 cap.toUInt64 kind == 1 then
            out := out.push { tagKind := kind, tagOff := i, tagLen := tagLen, attrOff := attrStart, attrLen := attrLen }
          i := closeIdx + 1
        else
          i := i + 1
      else
        i := i + 1
    else
      i := i + 1
  return out

/-- Zero-copy transcript turn span with 64-bit `xxh64Slice` + `leansys_transcript_index` digest. -/
structure TranscriptTurnSpan where
  turnOff : Nat
  turnLen : Nat
  digest  : UInt64
  deriving Repr, DecidableEq

/-- Zero-copy transcript turn indexer (`leansys_transcript_index`) computing per-turn 64-bit invalidation digests. -/
def indexTranscriptTurns (s : ByteSlice) : Array TranscriptTurnSpan := Id.run do
  let lines := JsonTape.splitJsonlLines s
  let cap := s.ba.size
  let mut out : Array TranscriptTurnSpan := #[]
  let mut prevDigest : UInt64 := 0
  for ln in lines do
    let blkHash := LeanSys.Hash.xxh64Slice ln
    let dig := verifyTranscriptIndex ln.off.toUInt64 ln.len.toUInt64 cap.toUInt64 prevDigest blkHash
    if dig != 0 then
      out := out.push { turnOff := ln.off, turnLen := ln.len, digest := dig }
      prevDigest := dig
  return out

end LeanSys.Codec
