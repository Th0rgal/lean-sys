/-
  LeanSys.Lsm: Sorted-String Table (SST) & 64-Bit Bloom Filter Storage Engine
  (`0 import Lean`, `0 sorryAx`)
  - Flushes `LeanSys.Store.Handle` live keys into an immutable sorted SST file (`state.sst`)
  - 24-byte SST footer: `magic : UInt32 := 0x4C535354 ("LSST")`, `numEntries : UInt32`,
    `indexOff : UInt64`, `bloomMask : UInt64`
  - Every `openSst` and `sstGet?` is gated by `LeanSys.Spec.verifySstBlock` (`leansys_verify_sst_block`)
  - O(1) Bloom negative filter + O(log N) binary search over sorted key slices
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Store

namespace LeanSys.Lsm

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Store

/-- Indexed entry inside an immutable SST image (`keyOff`/`keyLen` locate the key bytes in `rawBuf`). -/
structure SstIndexEntry where
  key    : String
  keyOff : Nat
  keyLen : Nat
  valOff : Nat
  valLen : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Opened SST table with verified footer, 64-bit Bloom filter mask, and sorted directory. -/
structure SstTable where
  path      : String
  rawBuf    : ByteArray
  bloomMask : UInt64
  entries   : Array SstIndexEntry
  deriving Inhabited

/-- Unsigned byte-wise compare of `buf[off, off+len)` against `q` (memcmp order, then length). -/
@[inline]
def compareKeyAt (buf : ByteArray) (off len : Nat) (q : ByteArray) : Ordering := Id.run do
  let n := Nat.min len q.size
  let mut i := 0
  while i < n do
    let a := buf.get! (off + i)
    let b := q.get! i
    if a != b then return (if a < b then .lt else .gt)
    i := i + 1
  return compare len q.size

/-- Byte-order (memcmp) less-than on UTF-8 keys; equals `String` code-point order. -/
@[inline]
def keyBytesLt (a b : ByteArray) : Bool :=
  compareKeyAt a 0 a.size b == .lt

namespace SstTable

/-- Flush all live `(key, value)` pairs from `Store.Handle` into an immutable sorted SST file at `sstPath`.
    Single pre-sized buffer, byte-order sort, footer gated by `verifySstBlock`. -/
def flushStore (st : Store.Handle) (sstPath : String) : IO (SysResult SstTable) := do
  let pairs := (st.kv.fold (fun acc k v => acc.push (k, k.toUTF8, v)) (Array.mkEmpty st.kv.size)).qsort
    (fun a b => keyBytesLt a.2.1 b.2.1)
  let mut cap := 24
  for (_, kb, v) in pairs do
    cap := cap + 12 + kb.size + v.size
  let mut buf := ByteArray.emptyWithCapacity cap
  let mut bloom : UInt64 := 0
  for (k, _, v) in pairs do
    bloom := bloomInsert bloom (xxh64String k)
    buf := v.copySlice 0 buf buf.size v.size false
  let indexOff := buf.size
  let mut entries : Array SstIndexEntry := Array.mkEmpty pairs.size
  let mut vOff := 0
  for (k, kb, v) in pairs do
    buf := pushUInt32LE buf kb.size.toUInt32
    buf := pushUInt32LE buf vOff.toUInt32
    buf := pushUInt32LE buf v.size.toUInt32
    let kOff := buf.size
    buf := kb.copySlice 0 buf buf.size kb.size false
    entries := entries.push { key := k, keyOff := kOff, keyLen := kb.size, valOff := vOff, valLen := v.size }
    vOff := vOff + v.size
  let footerOff := buf.size.toUInt64
  buf := pushUInt32LE buf sstMagic
  buf := pushUInt32LE buf entries.size.toUInt32
  buf := pushUInt64LE buf indexOff.toUInt64
  buf := pushUInt64LE buf bloom
  if verifySstBlock sstMagic entries.size.toUInt32 indexOff.toUInt64 footerOff buf.size.toUInt64 bloom != 1 then
    return .error .einval
  let tmpPath := sstPath ++ ".tmp"
  match ← withFd tmpPath 4 (fun fd => writeAll fd buf true) with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← atomicRename tmpPath sstPath with
    | .error e => pure (.error e)
    | .ok () => pure (.ok { path := sstPath, rawBuf := buf, bloomMask := bloom, entries := entries })

/-- Backwards-compatible name for `flushStore`. -/
@[inline]
def flushFromStore (st : Store.Handle) (sstPath : String) : IO (SysResult SstTable) :=
  flushStore st sstPath

/-- Open and verify an SST file from disk, gated by `leansys_verify_sst_block`. -/
def openSst (sstPath : String) : IO (SysResult SstTable) := do
  match ← withFd sstPath 0 (fun fd => do
    let buf ← preadByteArray fd 0 67108864
    pure (.ok buf)) with
  | .error e => pure (.error e)
  | .ok buf =>
    if buf.size < 24 then
      return .error .eio
    let footerOff := buf.size - 24
    let magic := readUInt32LE buf footerOff
    let numEntries := readUInt32LE buf (footerOff + 4)
    let indexOff := readUInt64LE buf (footerOff + 8)
    let bloom := readUInt64LE buf (footerOff + 16)
    if verifySstBlock magic numEntries indexOff footerOff.toUInt64 buf.size.toUInt64 bloom != 1 then
      return .error .einval
    let mut entries : Array SstIndexEntry := Array.mkEmpty numEntries.toNat
    let mut p := indexOff.toNat
    for _ in [0:numEntries.toNat] do
      if p + 12 > footerOff then
        return .error .eio
      let kLen := (readUInt32LE buf p).toNat
      let vOff := (readUInt32LE buf (p + 4)).toNat
      let vLen := (readUInt32LE buf (p + 8)).toNat
      if p + 12 + kLen > footerOff || vOff + vLen > indexOff.toNat then
        return .error .eio
      match String.fromUTF8? (buf.extract (p + 12) (p + 12 + kLen)) with
      | none => return .error .eio
      | some kStr =>
        if h : entries.size > 0 then
          let prev := entries[entries.size - 1]
          if compareKeyAt buf prev.keyOff prev.keyLen kStr.toUTF8 != .lt then
            return .error .eio
        entries := entries.push { key := kStr, keyOff := p + 12, keyLen := kLen, valOff := vOff, valLen := vLen }
      p := p + 12 + kLen
    return .ok { path := sstPath, rawBuf := buf, bloomMask := bloom, entries := entries }

/-- Query a key: 64-bit Bloom filter in O(1), then O(log N) binary search.
    Comparisons use the native `String` equality / order (`lean_string_dec_eq` / `lean_string_dec_lt`,
    UTF-8 byte order), which `openSst` has checked agrees with the on-disk `compareKeyAt` order. -/
def get? (tbl : SstTable) (key : String) : Option ByteSlice := Id.run do
  if !bloomContains tbl.bloomMask (xxh64String key) then
    return none
  let es := tbl.entries
  let mut lo : Nat := 0
  let mut hi : Nat := es.size
  while lo < hi do
    let mid := (lo + hi) >>> 1
    let e := es[mid]!
    if e.key == key then
      return if e.valOff + e.valLen ≤ tbl.rawBuf.size then
        some { ba := tbl.rawBuf, off := e.valOff, len := e.valLen } else none
    else if e.key < key then lo := mid + 1
    else hi := mid
  return none

/-- Compatibility alias for `get?`. -/
@[inline]
def getSlice? (tbl : SstTable) (key : String) : Option ByteSlice :=
  get? tbl key

/-- Lookup a UTF-8 string value by `key` in `SstTable`. -/
@[inline]
def getString? (tbl : SstTable) (key : String) : Option String :=
  (get? tbl key).map ByteSlice.toStringLossy

/-- Open an SST file in true index-only lazy mode (`rawBuf := ByteArray.empty`, `0 B` resident value RAM).
    Reads ONLY the 24-byte footer and the `[indexOff, footerOff)` directory slice via positional `preadByteArray`
    (never calling `openSst` or reading `[0, indexOff)` value pages into memory), gated by `verifySstBlock`
    and `verifyIosJetsamBudget`. -/
def openSstLazy (sstPath : String) : IO (SysResult SstTable) := do
  let fileLenOpt : Option Nat ← try
    let m ← (System.FilePath.mk sstPath).metadata
    pure (some m.byteSize.toNat)
  catch _ =>
    pure none
  let some fileLen := fileLenOpt | return .error .enoent
  if fileLen < 24 then
    return .error .eio
  let footerOff := fileLen - 24
  withFd sstPath 0 fun fd => do
    let footerBuf ← preadByteArray fd footerOff.toUInt64 24
    if footerBuf.size != 24 then
      return .error .eio
    let magic := readUInt32LE footerBuf 0
    let numEntries := readUInt32LE footerBuf 4
    let indexOff := readUInt64LE footerBuf 8
    let bloom := readUInt64LE footerBuf 16
    if verifySstBlock magic numEntries indexOff footerOff.toUInt64 fileLen.toUInt64 bloom != 1 then
      return .error .einval
    let idxLen := footerOff - indexOff.toNat
    let alignedIdxAlloc : UInt64 := (((idxLen + 24 + 16383) / 16384) * 16384).toUInt64
    if verifyIosJetsamBudget 0 alignedIdxAlloc 268435456 16383 0 != 1 then
      return .error .enospc
    let idxBuf ← preadByteArray fd indexOff idxLen
    if idxBuf.size != idxLen then
      return .error .eio
    let mut entries : Array SstIndexEntry := Array.mkEmpty numEntries.toNat
    let mut p := 0
    for _ in [0:numEntries.toNat] do
      if p + 12 > idxLen then
        return .error .eio
      let kLen := (readUInt32LE idxBuf p).toNat
      let vOff := (readUInt32LE idxBuf (p + 4)).toNat
      let vLen := (readUInt32LE idxBuf (p + 8)).toNat
      if p + 12 + kLen > idxLen || vOff + vLen > indexOff.toNat then
        return .error .eio
      match String.fromUTF8? (idxBuf.extract (p + 12) (p + 12 + kLen)) with
      | none => return .error .eio
      | some kStr =>
        if h : entries.size > 0 then
          let prev := entries[entries.size - 1]
          let prevRelOff := prev.keyOff - indexOff.toNat
          if compareKeyAt idxBuf prevRelOff prev.keyLen kStr.toUTF8 != .lt then
            return .error .eio
        entries := entries.push {
          key := kStr
          keyOff := indexOff.toNat + p + 12
          keyLen := kLen
          valOff := vOff
          valLen := vLen
        }
      p := p + 12 + kLen
    return .ok { path := sstPath, rawBuf := ByteArray.empty, bloomMask := bloom, entries := entries }

/-- Load an SST entry's value bytes from resident `rawBuf` when available, or via `preadByteArray`
    when the `SstTable` was opened with `openSstLazy` (`rawBuf.isEmpty`). Fails closed with `.eio`
    on short/corrupted reads so compaction and lazy search never silently drop keys. -/
def readEntryValue (tbl : SstTable) (e : SstIndexEntry) : IO (SysResult ByteArray) := do
  if !tbl.rawBuf.isEmpty then
    if e.valOff + e.valLen ≤ tbl.rawBuf.size then
      return .ok (tbl.rawBuf.extract e.valOff (e.valOff + e.valLen))
    else
      return .error .eio
  else if e.valLen == 0 then
    if tbl.path.isEmpty then return .error .einval
    else return .ok ByteArray.empty
  else
    if tbl.path.isEmpty then
      return .error .einval
    match ← withFd tbl.path 0 (fun fd => do
      let b ← preadByteArray fd e.valOff.toUInt64 e.valLen
      if b.size == e.valLen then pure (.ok b) else pure (.error .eio)) with
    | .ok b => return .ok b
    | .error err => return .error err

/-- Lookup a value by `key` in `SstTable` on resident or lazy (`openSstLazy`) handles, distinguishing
    clean key absence (`.ok none`) from short/corrupt disk read failures (`.error .eio`). -/
def getLazyResult (tbl : SstTable) (key : String) : IO (SysResult (Option ByteArray)) := do
  if !bloomContains tbl.bloomMask (xxh64String key) then
    return .ok none
  let es := tbl.entries
  let mut lo : Nat := 0
  let mut hi : Nat := es.size
  let mut found? : Option SstIndexEntry := none
  while lo < hi do
    let mid := (lo + hi) >>> 1
    let e := es[mid]!
    if e.key == key then
      found? := some e
      lo := hi
    else if e.key < key then lo := mid + 1
    else hi := mid
  match found? with
  | none => return .ok none
  | some e =>
    match ← readEntryValue tbl e with
    | .ok b => return .ok (some b)
    | .error err => return .error err

/-- Lookup a value by `key` in `SstTable`, using in-memory `rawBuf` when resident or lazy `preadByteArray`
    when opened via `openSstLazy`. -/
def getLazyIO? (tbl : SstTable) (key : String) : IO (Option ByteArray) := do
  match ← getLazyResult tbl key with
  | .ok v? => return v?
  | .error _ => return none

/-- Atomically flush `st` into a sorted SST file at `sstPath` and compact the WAL,
    returning the compacted `(Store.Handle × SstTable)` pair. -/
def flushAndCompactStore (st : Store.Handle) (sstPath : String) : IO (SysResult (Store.Handle × SstTable)) := do
  match ← flushStore st sstPath with
  | .error e => pure (.error e)
  | .ok tbl =>
    match ← Store.compact st with
    | .error e => pure (.error e)
    | .ok stCompacted => pure (.ok (stCompacted, tbl))

/-- Explicit 5-byte LSM tombstone sentinel (`0xFF 0x00 'D' 'E' 'L'`), matching `LeanSys.Table.tombstoneMarker`. -/
@[inline]
private def isSstTombstoneBytes (ba : ByteArray) (off len : Nat) : Bool :=
  len == 5 && off + 5 ≤ ba.size &&
  ba.get! off == 0xFF &&
  ba.get! (off + 1) == 0x00 &&
  ba.get! (off + 2) == 0x44 &&
  ba.get! (off + 3) == 0x45 &&
  ba.get! (off + 4) == 0x4C

/-- Maximum SST file size (`64 MiB`), matching `openSst`'s bounded resident read cap
    and ensuring 32-bit `kLen`/`vOff`/`vLen`/`numEntries` directory fields never wrap. -/
def maxSstFileBytes : Nat := 67108864

/-- Write a pre-sorted, deduplicated array of `(key, keyUtf8, valBytes)` entries into an immutable SST file at `outPath`,
    gated by `maxSstFileBytes`, `leansys_verify_sst_block`, and atomic `rename`. -/
def writeSortedPairs (pairs : Array (String × ByteArray × ByteArray)) (outPath : String) : IO (SysResult SstTable) := do
  if verifySliceBounds 0 pairs.size.toUInt64 0xFFFFFFFF != 1 then
    return .error .enospc
  let mut cap := 24
  for (_, kb, v) in pairs do
    if verifySliceBounds 0 kb.size.toUInt64 maxSstFileBytes.toUInt64 != 1 ||
       verifySliceBounds 0 v.size.toUInt64 maxSstFileBytes.toUInt64 != 1 ||
       verifySliceBounds cap.toUInt64 (12 + kb.size + v.size).toUInt64 maxSstFileBytes.toUInt64 != 1 then
      return .error .enospc
    cap := cap + 12 + kb.size + v.size
  let mut buf := ByteArray.emptyWithCapacity cap
  let mut bloom : UInt64 := 0
  for (k, _, v) in pairs do
    bloom := bloomInsert bloom (xxh64String k)
    buf := v.copySlice 0 buf buf.size v.size false
  let indexOff := buf.size
  let mut entries : Array SstIndexEntry := Array.mkEmpty pairs.size
  let mut vOff := 0
  for (k, kb, v) in pairs do
    buf := pushUInt32LE buf kb.size.toUInt32
    buf := pushUInt32LE buf vOff.toUInt32
    buf := pushUInt32LE buf v.size.toUInt32
    let kOff := buf.size
    buf := kb.copySlice 0 buf buf.size kb.size false
    entries := entries.push { key := k, keyOff := kOff, keyLen := kb.size, valOff := vOff, valLen := v.size }
    vOff := vOff + v.size
  let footerOff := buf.size.toUInt64
  buf := pushUInt32LE buf sstMagic
  buf := pushUInt32LE buf entries.size.toUInt32
  buf := pushUInt64LE buf indexOff.toUInt64
  buf := pushUInt64LE buf bloom
  if verifySstBlock sstMagic entries.size.toUInt32 indexOff.toUInt64 footerOff buf.size.toUInt64 bloom != 1 then
    return .error .einval
  let tmpPath := outPath ++ ".tmp"
  match ← withFd tmpPath 4 (fun fd => writeAll fd buf true) with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← atomicRename tmpPath outPath with
    | .error e => pure (.error e)
    | .ok () => pure (.ok { path := outPath, rawBuf := buf, bloomMask := bloom, entries := entries })

/-- Two-way sorted SST compaction (`older` + `newer` → `outPath`) gated by `LeanSys.Spec.verifyCompactionWinner`:
    - Linear `O(|older| + |newer|)` merge scan over already-sorted SST directories.
    - When both tables contain `key`, `newer` strictly wins (never resurrecting `older` when `newer` is a tombstone!).
    - When `dropTombstones := true` (bottom-most level compaction), winning tombstones are dropped cleanly. -/
def mergeTables (older newer : SstTable) (outPath : String) (dropTombstones : Bool := false) :
    IO (SysResult SstTable) := do
  let esOld := older.entries
  let esNew := newer.entries
  let mut merged : Array (String × ByteArray × ByteArray) := Array.mkEmpty (esOld.size + esNew.size)
  let mut i : Nat := 0
  let mut j : Nat := 0
  let dropFlag : UInt8 := if dropTombstones then 1 else 0
  while i < esOld.size || j < esNew.size do
    if i < esOld.size && j < esNew.size then
      let eo := esOld[i]!
      let en := esNew[j]!
      if eo.key == en.key then
        let .ok vo ← readEntryValue older eo | return .error .eio
        let .ok vn ← readEntryValue newer en | return .error .eio
        let oTomb : UInt8 := if isSstTombstoneBytes vo 0 vo.size then 1 else 0
        let nTomb : UInt8 := if isSstTombstoneBytes vn 0 vn.size then 1 else 0
        let win := verifyCompactionWinner 1 nTomb 1 oTomb dropFlag
        if win == 2 then
          merged := merged.push (en.key, en.key.toUTF8, vn)
        i := i + 1
        j := j + 1
      else if keyBytesLt eo.key.toUTF8 en.key.toUTF8 then
        let .ok vo ← readEntryValue older eo | return .error .eio
        let oTomb : UInt8 := if isSstTombstoneBytes vo 0 vo.size then 1 else 0
        if verifyCompactionWinner 0 0 1 oTomb dropFlag == 1 then
          merged := merged.push (eo.key, eo.key.toUTF8, vo)
        i := i + 1
      else
        let .ok vn ← readEntryValue newer en | return .error .eio
        let nTomb : UInt8 := if isSstTombstoneBytes vn 0 vn.size then 1 else 0
        if verifyCompactionWinner 1 nTomb 0 0 dropFlag == 2 then
          merged := merged.push (en.key, en.key.toUTF8, vn)
        j := j + 1
    else if i < esOld.size then
      let eo := esOld[i]!
      let .ok vo ← readEntryValue older eo | return .error .eio
      let oTomb : UInt8 := if isSstTombstoneBytes vo 0 vo.size then 1 else 0
      if verifyCompactionWinner 0 0 1 oTomb dropFlag == 1 then
        merged := merged.push (eo.key, eo.key.toUTF8, vo)
      i := i + 1
    else
      let en := esNew[j]!
      let .ok vn ← readEntryValue newer en | return .error .eio
      let nTomb : UInt8 := if isSstTombstoneBytes vn 0 vn.size then 1 else 0
      if verifyCompactionWinner 1 nTomb 0 0 dropFlag == 2 then
        merged := merged.push (en.key, en.key.toUTF8, vn)
      j := j + 1
  writeSortedPairs merged outPath

/-- Multi-level SST compaction (`tablesOldestToNewest` → `outPath`):
    folds `mergeTables` from oldest to newest, applying `dropTombstones` only on the final pass
    so intermediate merges never lose tombstones that must still mask older generations! -/
def compactLevels (tablesOldestToNewest : Array SstTable) (outPath : String)
    (dropTombstones : Bool := true) : IO (SysResult SstTable) := do
  if tablesOldestToNewest.isEmpty then
    writeSortedPairs #[] outPath
  else if tablesOldestToNewest.size == 1 then
    let only := tablesOldestToNewest[0]!
    if !dropTombstones && only.path == outPath then
      return .ok only
    let emptyTbl : SstTable := { path := "", rawBuf := ByteArray.empty, bloomMask := 0, entries := #[] }
    mergeTables emptyTbl only outPath dropTombstones
  else
    let mut acc := tablesOldestToNewest[0]!
    let lastIdx := tablesOldestToNewest.size - 1
    for k in [1:tablesOldestToNewest.size] do
      let isFinal := k == lastIdx
      let stepPath := if isFinal then outPath else s!"{outPath}.merge.{k}"
      let stepDrop := if isFinal then dropTombstones else false
      match ← mergeTables acc tablesOldestToNewest[k]! stepPath stepDrop with
      | .error e => return .error e
      | .ok nextTbl =>
        if k > 1 then
          discard <| unlinkFile s!"{outPath}.merge.{k - 1}"
        acc := nextTbl
    if tablesOldestToNewest.size > 2 then
      discard <| unlinkFile s!"{outPath}.merge.{lastIdx - 1}"
    return .ok acc

end SstTable

end LeanSys.Lsm
