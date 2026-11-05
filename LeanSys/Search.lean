/-
  LeanSys.Search: Pure-Lean Trigram & Token Inverted SST Index (`0 import Lean`, `0 sorryAx`)
  - Replaces SQLite FTS5 for mission/transcript/event search with zero C dependencies (`0 sqlite`)
  - Extracts deduplicated ASCII-lowercased 24-bit trigrams (`(b0 <<< 16) | (b1 <<< 8) | b2`)
  - Stores postings as sorted keys `tri:<6hex>:<docId>` and document snapshots `doc:<docId>` in `Store.Handle` / `SstTable`
  - Gated by `LeanSys.Spec.verifyTrigramCandidate` (`noFalseNegatives` invariant) with exact post-filter verification
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Store
import LeanSys.Lsm
import LeanSys.Table

namespace LeanSys.Search

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Store
open LeanSys.Lsm

/-- Lowercase an ASCII byte (`'A'..'Z'` → `'a'..'z'`), leaving UTF-8 multi-byte sequences intact. -/
@[inline]
def asciiLowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- Lowercase all ASCII bytes in `ba`. -/
def asciiLowerBytes (ba : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity ba.size
  for i in [0:ba.size] do
    out := out.push (asciiLowerByte (ba.get! i))
  return out

/-- Format a 24-bit trigram word (`0..0xFFFFFF`) as a fixed 6-character uppercase hex key component. -/
def hex6BE (tri : UInt32) : String := Id.run do
  let mut s := ""
  for i in [0:6] do
    let shift : UInt32 := ((5 - i) * 4).toUInt32
    let nib := ((tri >>> shift) &&& 0xF).toNat
    let ch := if nib < 10 then Char.ofNat (48 + nib) else Char.ofNat (55 + nib)
    s := s.push ch
  return s

/-- Extract sorted, deduplicated 24-bit ASCII-lowercased trigrams from `text`. -/
def extractTrigrams (text : String) : Array UInt32 := Id.run do
  let b := asciiLowerBytes text.toUTF8
  if b.size < 3 then
    return #[]
  let n := b.size - 2
  let mut raw : Array UInt32 := Array.mkEmpty n
  for i in [0:n] do
    let w : UInt32 :=
      ((b.get! i).toUInt32 <<< 16) |||
      ((b.get! (i + 1)).toUInt32 <<< 8) |||
      (b.get! (i + 2)).toUInt32
    raw := raw.push w
  let sorted := raw.qsort (fun a c => a < c)
  let mut dedup : Array UInt32 := Array.mkEmpty sorted.size
  for w in sorted do
    if h : dedup.size > 0 then
      if dedup[dedup.size - 1] != w then
        dedup := dedup.push w
    else
      dedup := dedup.push w
  return dedup

/-- Exact case-insensitive ASCII substring check (`needleLower` already lowercased). -/
def containsBytesLower (haystack : ByteArray) (needleLower : ByteArray) : Bool := Id.run do
  if needleLower.isEmpty then return true
  if haystack.size < needleLower.size then return false
  let limit := haystack.size - needleLower.size + 1
  for i in [0:limit] do
    let mut matched := true
    for j in [0:needleLower.size] do
      if asciiLowerByte (haystack.get! (i + j)) != needleLower.get! j then
        matched := false
        break
    if matched then return true
  return false

/-- Index a document `(docId, text)` into `st`, writing `doc:<docId>` and all `tri:<6hex>:<docId>` postings in a single WAL batch. -/
def indexDoc (st : Store.Handle) (docId : String) (text : String) (sync : Bool := false) :
    IO (SysResult Store.Handle) := do
  if docId.isEmpty then
    return .error .einval
  let tris := extractTrigrams text
  let mut batch : Array (String × ByteSlice) := Array.mkEmpty (tris.size + 1)
  batch := batch.push (s!"doc:{docId}", ByteSlice.ofString text)
  let marker := ByteSlice.ofString "1"
  for tri in tris do
    batch := batch.push (s!"tri:{hex6BE tri}:{docId}", marker)
  Store.putBatch st batch sync

/-- `true` iff `tbl` was opened lazily (`openSstLazy`) with non-empty directory entries and an unpopulated `rawBuf`. -/
@[inline]
def isNonResidentLazy (tbl : SstTable) : Bool :=
  tbl.rawBuf.isEmpty && !tbl.entries.isEmpty

/-- Collect all `docId` postings matching prefix `tri:<6hex>:` in sorted order via binary search on resident `tbl.entries`. -/
def lookupTrigramPostings (tbl : SstTable) (tri : UInt32) : Array String := Id.run do
  let prefixStr := s!"tri:{hex6BE tri}:"
  let prefixLen := prefixStr.utf8ByteSize
  let es := tbl.entries
  let mut lo : Nat := 0
  let mut hi : Nat := es.size
  while lo < hi do
    let mid := (lo + hi) >>> 1
    if es[mid]!.key < prefixStr then lo := mid + 1 else hi := mid
  let mut docs : Array String := #[]
  let mut idx := lo
  while idx < es.size do
    let e := es[idx]!
    if !e.key.startsWith prefixStr then break
    if e.valOff + e.valLen ≤ tbl.rawBuf.size then
      let sl : ByteSlice := { ba := tbl.rawBuf, off := e.valOff, len := e.valLen }
      if !LeanSys.Table.isTombstoneSlice sl then
        let docId := String.fromUTF8! (e.key.toUTF8.extract prefixLen e.key.utf8ByteSize)
        docs := docs.push docId
    idx := idx + 1
  return docs

/-- Collect all `docId` postings matching prefix `tri:<6hex>:` on either resident (`openSst`) or lazy (`openSstLazy`) tables. -/
def lookupTrigramPostingsIO (tbl : SstTable) (tri : UInt32) : IO (SysResult (Array String)) := do
  let prefixStr := s!"tri:{hex6BE tri}:"
  let prefixLen := prefixStr.utf8ByteSize
  let es := tbl.entries
  let mut lo : Nat := 0
  let mut hi : Nat := es.size
  while lo < hi do
    let mid := (lo + hi) >>> 1
    if es[mid]!.key < prefixStr then lo := mid + 1 else hi := mid
  let mut docs : Array String := #[]
  let mut idx := lo
  while idx < es.size do
    let e := es[idx]!
    if !e.key.startsWith prefixStr then break
    let .ok valBytes ← SstTable.readEntryValue tbl e | return .error .eio
    if !LeanSys.Table.isTombstoneSlice (ByteSlice.ofByteArray valBytes) then
      let docId := String.fromUTF8! (e.key.toUTF8.extract prefixLen e.key.utf8ByteSize)
      docs := docs.push docId
    idx := idx + 1
  return .ok docs

/-- Intersect two sorted `Array String` posting lists in `O(|a| + |b|)`. -/
def intersectSortedPostings (a b : Array String) : Array String := Id.run do
  let mut out : Array String := Array.mkEmpty (Nat.min a.size b.size)
  let mut i : Nat := 0
  let mut j : Nat := 0
  while i < a.size && j < b.size do
    let da := a[i]!
    let db := b[j]!
    if da == db then
      out := out.push da
      i := i + 1
      j := j + 1
    else if da < db then
      i := i + 1
    else
      j := j + 1
  return out

/-- Search a resident `SstTable` (`openSst` / `flushStore`) for case-insensitive substring `query`,
    returning up to `limit` matching `(docId, docText)` pairs:
    - Queries with `≥ 3` ASCII bytes intersect sorted `tri:<6hex>:` posting lists first, then verify via `verifyTrigramCandidate` + `containsBytesLower`.
    - Short queries (`1..2` bytes) scan `doc:` entries with `containsBytesLower` so short substrings also have zero false negatives.
    - Note: For lazy SSTs (`openSstLazy`), call `searchTrigramSstIO` (or `searchTrigramSst?` which rejects non-resident tables with `none`). -/
def searchTrigramSst (tbl : SstTable) (query : String) (limit : Nat := 64) : Array (String × String) := Id.run do
  if limit == 0 || query.isEmpty || isNonResidentLazy tbl then
    return #[]
  let qLower := asciiLowerBytes query.toUTF8
  let qTris := extractTrigrams query
  if qTris.isEmpty then
    -- Short query (< 3 bytes): scan `doc:` prefix in `tbl`
    let docPrefix := "doc:"
    let es := tbl.entries
    let mut lo : Nat := 0
    let mut hi : Nat := es.size
    while lo < hi do
      let mid := (lo + hi) >>> 1
      if es[mid]!.key < docPrefix then lo := mid + 1 else hi := mid
    let mut out : Array (String × String) := #[]
    let mut idx := lo
    while idx < es.size && out.size < limit do
      let e := es[idx]!
      if !e.key.startsWith docPrefix then break
      if e.valOff + e.valLen ≤ tbl.rawBuf.size then
        let docSlice : ByteSlice := { ba := tbl.rawBuf, off := e.valOff, len := e.valLen }
        if !LeanSys.Table.isTombstoneSlice docSlice then
          let docBytes := docSlice.toByteArray
          if verifyTrigramCandidate 0 0 docBytes.size.toUInt64 == 1 && containsBytesLower docBytes qLower then
            let docId := String.fromUTF8! (e.key.toUTF8.extract 4 e.key.utf8ByteSize)
            out := out.push (docId, String.fromUTF8? docBytes |>.getD "")
      idx := idx + 1
    return out
  else
    let mut cands := lookupTrigramPostings tbl qTris[0]!
    for k in [1:qTris.size] do
      if cands.isEmpty then break
      cands := intersectSortedPostings cands (lookupTrigramPostings tbl qTris[k]!)
    let mut out : Array (String × String) := Array.mkEmpty (Nat.min cands.size limit)
    for docId in cands do
      if out.size >= limit then break
      if let some docSlice := SstTable.get? tbl s!"doc:{docId}" then
        if !LeanSys.Table.isTombstoneSlice docSlice then
          let docBytes := docSlice.toByteArray
          if verifyTrigramCandidate qTris.size.toUInt32 qTris.size.toUInt32 docBytes.size.toUInt64 == 1 &&
             containsBytesLower docBytes qLower then
            out := out.push (docId, String.fromUTF8? docBytes |>.getD "")
    return out

/-- Pure resident search wrapper that returns `none` when `tbl` is a non-resident `openSstLazy` handle
    (preventing callers from confusing an unloaded lazy handle with zero search matches). -/
def searchTrigramSst? (tbl : SstTable) (query : String) (limit : Nat := 64) : Option (Array (String × String)) :=
  if isNonResidentLazy tbl then none else some (searchTrigramSst tbl query limit)

/-- Search any `SstTable` (both resident `openSst` and on-demand `openSstLazy` via `preadByteArray`)
    for case-insensitive substring `query`, preserving zero false negatives (`noFalseNegatives`). -/
def searchTrigramSstIO (tbl : SstTable) (query : String) (limit : Nat := 64) : IO (SysResult (Array (String × String))) := do
  if limit == 0 || query.isEmpty then
    return .ok #[]
  if !isNonResidentLazy tbl then
    return .ok (searchTrigramSst tbl query limit)
  let qLower := asciiLowerBytes query.toUTF8
  let qTris := extractTrigrams query
  if qTris.isEmpty then
    let docPrefix := "doc:"
    let es := tbl.entries
    let mut lo : Nat := 0
    let mut hi : Nat := es.size
    while lo < hi do
      let mid := (lo + hi) >>> 1
      if es[mid]!.key < docPrefix then lo := mid + 1 else hi := mid
    let mut out : Array (String × String) := #[]
    let mut idx := lo
    while idx < es.size && out.size < limit do
      let e := es[idx]!
      if !e.key.startsWith docPrefix then break
      let .ok docBytes ← SstTable.readEntryValue tbl e | return .error .eio
      if !LeanSys.Table.isTombstoneSlice (ByteSlice.ofByteArray docBytes) then
        if verifyTrigramCandidate 0 0 docBytes.size.toUInt64 == 1 && containsBytesLower docBytes qLower then
          let docId := String.fromUTF8! (e.key.toUTF8.extract 4 e.key.utf8ByteSize)
          out := out.push (docId, String.fromUTF8? docBytes |>.getD "")
      idx := idx + 1
    return .ok out
  else
    let .ok firstPostings ← lookupTrigramPostingsIO tbl qTris[0]! | return .error .eio
    let mut cands := firstPostings
    for k in [1:qTris.size] do
      if cands.isEmpty then break
      let .ok nextPostings ← lookupTrigramPostingsIO tbl qTris[k]! | return .error .eio
      cands := intersectSortedPostings cands nextPostings
    let mut out : Array (String × String) := Array.mkEmpty (Nat.min cands.size limit)
    for docId in cands do
      if out.size >= limit then break
      match ← SstTable.getLazyIO? tbl s!"doc:{docId}" with
      | none => return .error .eio
      | some docBytes =>
        if !LeanSys.Table.isTombstoneSlice (ByteSlice.ofByteArray docBytes) then
          if verifyTrigramCandidate qTris.size.toUInt32 qTris.size.toUInt32 docBytes.size.toUInt64 == 1 &&
             containsBytesLower docBytes qLower then
            out := out.push (docId, String.fromUTF8? docBytes |>.getD "")
    return .ok out

/-- Direct in-memory substring search over live `doc:<docId>` entries in a `Store.Handle` (before SST flush). -/
def searchStoreSubstring (st : Store.Handle) (query : String) (limit : Nat := 64) : Array (String × String) := Id.run do
  if limit == 0 || query.isEmpty then
    return #[]
  let qLower := asciiLowerBytes query.toUTF8
  let matchesArr := st.kv.fold (fun acc k v =>
    if acc.size < limit && k.startsWith "doc:" && !LeanSys.Table.isTombstoneSlice (ByteSlice.ofByteArray v) &&
       containsBytesLower v qLower then
      let docId := String.fromUTF8! (k.toUTF8.extract 4 k.utf8ByteSize)
      acc.push (docId, String.fromUTF8? v |>.getD "")
    else acc) #[]
  return matchesArr.qsort (fun a b => a.1 < b.1)

end LeanSys.Search
