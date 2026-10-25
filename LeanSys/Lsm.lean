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

/-- Open an SST file in zero-value-RAM mode (`rawBuf := ByteArray.empty`), retaining only the
    verified index directory + Bloom filter mask so mobile/iOS callers under Jetsam limits never
    hold value pages in dirty heap memory. -/
def openSstLazy (sstPath : String) : IO (SysResult SstTable) := do
  match ← openSst sstPath with
  | .error e => pure (.error e)
  | .ok tbl => pure (.ok { tbl with rawBuf := ByteArray.empty })

/-- Lookup a value by `key` in `SstTable`, using in-memory `rawBuf` when resident or lazy `preadByteArray`
    when opened via `openSstLazy`. -/
def getLazyIO? (tbl : SstTable) (key : String) : IO (Option ByteArray) := do
  if !bloomContains tbl.bloomMask (xxh64String key) then
    return none
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
  | none => return none
  | some e =>
    if e.valOff + e.valLen ≤ tbl.rawBuf.size then
      return some (tbl.rawBuf.extract e.valOff (e.valOff + e.valLen))
    else
      match ← withFd tbl.path 0 (fun fd => do
        let b ← preadByteArray fd e.valOff.toUInt64 e.valLen
        pure (.ok b)) with
      | .ok b => return if b.size == e.valLen then some b else none
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

end SstTable

end LeanSys.Lsm
