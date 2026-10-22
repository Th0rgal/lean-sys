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

/-- Indexed entry inside an immutable SST image. -/
structure SstIndexEntry where
  key    : String
  valOff : Nat
  valLen : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Opened SST table with verified footer, 64-bit Bloom filter mask, and sorted directory. -/
structure SstTable where
  path      : String
  rawBuf    : ByteArray
  bloomMask : UInt64
  entries   : Array SstIndexEntry

namespace SstTable

/-- Flush all live `(key, value)` pairs from `Store.Handle` into an immutable sorted SST file at `sstPath`. -/
def flushFromStore (st : Store.Handle) (sstPath : String) : IO (SysResult SstTable) := do
  let pairs := st.kv.toList.toArray.qsort (fun a b => a.1 < b.1)
  let mut dataBuf := ByteArray.empty
  let mut idxEntries : Array SstIndexEntry := Array.mkEmpty pairs.size
  let mut bloom : UInt64 := 0
  for (k, v) in pairs do
    let kh := xxh64String k
    bloom := bloomInsert bloom kh
    let valOff := dataBuf.size
    let valLen := v.size
    dataBuf := dataBuf ++ v
    idxEntries := idxEntries.push { key := k, valOff := valOff, valLen := valLen }
  let indexOff := dataBuf.size.toUInt64
  for e in idxEntries do
    let kb := e.key.toUTF8
    dataBuf := pushUInt32LE dataBuf kb.size.toUInt32
    dataBuf := pushUInt32LE dataBuf e.valOff.toUInt32
    dataBuf := pushUInt32LE dataBuf e.valLen.toUInt32
    dataBuf := dataBuf ++ kb
  let footerOff := dataBuf.size.toUInt64
  dataBuf := pushUInt32LE dataBuf sstMagic
  dataBuf := pushUInt32LE dataBuf idxEntries.size.toUInt32
  dataBuf := pushUInt64LE dataBuf indexOff
  dataBuf := pushUInt64LE dataBuf bloom
  let fileSize := dataBuf.size.toUInt64
  if verifySstBlock sstMagic idxEntries.size.toUInt32 indexOff footerOff fileSize bloom != 1 then
    return .error .einval
  let tmpPath := sstPath ++ ".tmp"
  match ← withFd tmpPath 4 (fun fd => writeAll fd dataBuf true) with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← atomicRename tmpPath sstPath with
    | .error e => pure (.error e)
    | .ok () =>
      pure (.ok {
        path := sstPath
        rawBuf := dataBuf
        bloomMask := bloom
        entries := idxEntries
      })

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
      let kStr := String.fromUTF8! (buf.extract (p + 12) (p + 12 + kLen))
      entries := entries.push { key := kStr, valOff := vOff, valLen := vLen }
      p := p + 12 + kLen
    return .ok {
      path := sstPath
      rawBuf := buf
      bloomMask := bloom
      entries := entries
    }

/-- Query a key in `SstTable`: checks the 64-bit Bloom filter in O(1), then binary-searches `entries` in O(log N). -/
def getSlice? (tbl : SstTable) (key : String) : Option ByteSlice := Id.run do
  let kh := xxh64String key
  if !bloomContains tbl.bloomMask kh then
    return none
  let n := tbl.entries.size
  if n == 0 then return none
  let mut lo : Nat := 0
  let mut hi : Nat := n
  while lo < hi do
    let mid := (lo + hi) / 2
    let e := tbl.entries[mid]!
    if e.key == key then
      return ByteSlice.subSlice? (ByteSlice.ofByteArray tbl.rawBuf) e.valOff e.valLen
    else if e.key < key then
      lo := mid + 1
    else
      hi := mid
  return none

/-- Lookup a UTF-8 string value by `key` in `SstTable`. -/
@[inline]
def getString? (tbl : SstTable) (key : String) : Option String :=
  (getSlice? tbl key).map ByteSlice.toStringLossy

end SstTable

end LeanSys.Lsm
