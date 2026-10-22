/-
  LeanSys.Table: Order-Preserving Big-Endian Composite 192-Bit Keys & Range Scan over `SstTable`
  (`0 import Lean`, `0 sorryAx`)
  - Encodes `(hi64, lo64, seq64)` as a 48-char uppercase hex big-endian string key so standard
    byte-order (`memcmp`) sorting in `LeanSys.Lsm.SstTable` matches lexicographic `(hi, lo, seq)` order
  - Every range scan and key ordering check is gated by
    `LeanSys.Spec.verifyCompositeKeyOrder` (`leansys_verify_composite_key_order`)
  - Enables SQLite-free `(mission_id, seq)` event range queries and `(project_slug_hash, track_hash, seq)` scans
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Store
import LeanSys.Lsm

namespace LeanSys.Table

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Store
open LeanSys.Lsm

/-- 192-bit composite key `(hi, lo, seq)` for ordered range indexes (e.g., `(uuid_hi, uuid_lo, seq)`). -/
structure CompositeKey where
  hi  : UInt64
  lo  : UInt64
  seq : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace CompositeKey

/-- Convert a 4-bit nibble (`0..15`) to its uppercase ASCII hex character. -/
@[inline]
def nibbleChar (n : UInt64) : Char :=
  let v := (n &&& 0xF).toNat
  if v < 10 then Char.ofNat (48 + v) else Char.ofNat (55 + v)

/-- Encode a `UInt64` as a fixed-width 16-character big-endian uppercase hex string. -/
def hex16BE (w : UInt64) : String := Id.run do
  let mut s := ""
  for i in [0:16] do
    let shift : UInt64 := ((15 - i) * 4).toUInt64
    s := s.push (nibbleChar (w >>> shift))
  return s

/-- Encode a `CompositeKey` as a 48-character big-endian hex string (`HHHHHHHHHHHHHHHH:LLLLLLLLLLLLLLLL:SSSSSSSSSSSSSSSS`). -/
def encode (k : CompositeKey) : String :=
  s!"{hex16BE k.hi}:{hex16BE k.lo}:{hex16BE k.seq}"

/-- Construct a `CompositeKey` from two string namespaces `(ns, track)` and a monotonic `seq`. -/
@[inline]
def ofNamespace (ns track : String) (seq : UInt64) : CompositeKey :=
  { hi := xxh64String ns, lo := xxh64String track, seq := seq }

/-- Check `a ≤ b` via the unboxed C-ABI gate `leansys_verify_composite_key_order`. -/
@[inline]
def le (a b : CompositeKey) : Bool :=
  verifyCompositeKeyOrder a.hi a.lo a.seq b.hi b.lo b.seq == 1

end CompositeKey

/-- Put a `(CompositeKey, payload)` record into a `LeanSys.Store.Handle`. -/
@[inline]
def putComposite (st : Store.Handle) (k : CompositeKey) (val : ByteSlice) (sync : Bool := false) : IO (SysResult Store.Handle) :=
  Store.put st (CompositeKey.encode k) val sync

/-- Point lookup of a `CompositeKey` in an `SstTable`. -/
@[inline]
def getComposite? (tbl : SstTable) (k : CompositeKey) : Option ByteSlice :=
  SstTable.get? tbl (CompositeKey.encode k)

/--
  Verified prefix & range scan over `SstTable` between `[loKey, hiKey]` (inclusive),
  returning up to `limit` matching `(keyStr, valueSlice)` pairs in ascending order.
  Gated by `leansys_verify_composite_key_order`.
-/
def rangeScan (tbl : SstTable) (loKey hiKey : CompositeKey) (limit : Nat := 256) : Array (String × ByteSlice) := Id.run do
  if !CompositeKey.le loKey hiKey || limit == 0 then
    return #[]
  let loStr := CompositeKey.encode loKey
  let hiStr := CompositeKey.encode hiKey
  let es := tbl.entries
  -- Binary search for the lower bound `e.key ≥ loStr`
  let mut l : Nat := 0
  let mut r : Nat := es.size
  while l < r do
    let mid := (l + r) >>> 1
    let e := es[mid]!
    if e.key < loStr then
      l := mid + 1
    else
      r := mid
  let mut out : Array (String × ByteSlice) := Array.mkEmpty (Nat.min limit 32)
  let mut idx := l
  while idx < es.size && out.size < limit do
    let e := es[idx]!
    if hiStr < e.key then
      break
    if e.valOff + e.valLen ≤ tbl.rawBuf.size then
      out := out.push (e.key, { ba := tbl.rawBuf, off := e.valOff, len := e.valLen })
    idx := idx + 1
  return out

end LeanSys.Table
