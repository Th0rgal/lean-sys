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
    let c := ba.get! p
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
    let c := ba.get! p
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
    let c := ba.get! p
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
  if p < limit && ba.get! p == 123 then -- '{'
    p := p + 1
  while p < limit do
    p := skipWs ba p limit
    if p ≥ limit then break
    let c := ba.get! p
    if c == 125 then break -- '}'
    if c == 44 then -- ','
      p := skipWs ba (p + 1) limit
    if p ≥ limit || ba.get! p != 34 then
      p := p + 1
    else
      let keyStart := p + 1
      match scanQuotedString ba keyStart limit with
      | none => break
      | some keyEnd =>
        let keyLen := keyEnd - keyStart
        p := skipWs ba (keyEnd + 1) limit
        if p ≥ limit || ba.get! p != 58 then -- ':'
          break
        p := skipWs ba (p + 1) limit
        if p ≥ limit then break
        if ba.get! p == 34 then -- string value
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

/-- Check if `[off, off + len)` in `ba` matches `targetBytes` byte-for-byte without allocation. -/
@[inline]
def sliceEqBytes (ba : ByteArray) (off len : Nat) (targetBytes : ByteArray) : Bool := Id.run do
  if len != targetBytes.size || off + len > ba.size then return false
  for i in [0:len] do
    if ba.get! (off + i) != targetBytes.get! i then return false
  return true

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
  let (sl, _) ← lookupSlice? tape key
  some sl.toStringLossy

/-- Lookup an unsigned `Nat` field in `tape` by `key` directly from ASCII digits in the slice. -/
def lookupNat? (tape : JsonTape) (key : String) : Option Nat := Id.run do
  let some (sl, _) := lookupSlice? tape key | return none
  if sl.len == 0 then return none
  let mut acc : Nat := 0
  let mut foundDigit := false
  let endOff := Nat.min (sl.off + sl.len) sl.ba.size
  for i in [sl.off:endOff] do
    let b := sl.ba.get! i
    if 48 ≤ b && b ≤ 57 then
      acc := acc * 10 + (b - 48).toNat
      foundDigit := true
    else
      break
  return if foundDigit then some acc else none

/-- Lookup a boolean field (`true` / `false`) in `tape` by `key` without allocation. -/
def lookupBool? (tape : JsonTape) (key : String) : Option Bool := do
  let (sl, _) ← lookupSlice? tape key
  if sl.len == 4 && sl.getByteD 0 == 116 && sl.getByteD 1 == 114 then -- "tr..."
    some true
  else if sl.len == 5 && sl.getByteD 0 == 102 && sl.getByteD 1 == 97 then -- "fa..."
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
    if ba.get! i == 10 then -- '\n'
      let rawLen := i - lineStart
      let effLen := if rawLen > 0 && ba.get! (lineStart + rawLen - 1) == 13 then rawLen - 1 else rawLen
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

end LeanSys.Codec
