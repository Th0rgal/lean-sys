/-
  LeanSys.Store: Crash-Atomic Append-Only WAL, In-Memory KV Index, and Hardlinked CAS
  (`0 import Lean`, `0 sorryAx`)
  - 16-byte WAL frame header: `magic : UInt32 := 0x4C535953 ("LSYS")`, `payloadLen : UInt32`,
    `fnv1a64 : UInt64`, followed by `payload : ByteArray` (`keyLen : UInt32` + `key` + `val`).
  - Every `Store.open` replays frames through `leansys_verify_wal_frame`, truncating torn tails.
  - Atomic compaction (`Store.compact`) writes a fresh WAL to `.tmp`, `fsync`s, and atomically `rename`s.
  - Content-Addressable Store (`Store.casPut`, `Store.casMaterialize`) with path-traversal gate.
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import Std.Data.HashMap

namespace LeanSys.Store

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash

/-! ## Binary Little-Endian Packing Helpers (`UInt32` / `UInt64`) -/

@[inline]
def pushUInt32LE (ba : ByteArray) (v : UInt32) : ByteArray :=
  ba.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8

@[inline]
def pushUInt64LE (ba : ByteArray) (v : UInt64) : ByteArray :=
  ba.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8
    |>.push ((v >>> 32) &&& 0xFF).toUInt8
    |>.push ((v >>> 40) &&& 0xFF).toUInt8
    |>.push ((v >>> 48) &&& 0xFF).toUInt8
    |>.push ((v >>> 56) &&& 0xFF).toUInt8

@[inline]
def readUInt32LE (ba : ByteArray) (off : Nat) : UInt32 :=
  if off + 4 ≤ ba.size then
    let b0 := (ba.get! off).toUInt32
    let b1 := (ba.get! (off + 1)).toUInt32 <<< 8
    let b2 := (ba.get! (off + 2)).toUInt32 <<< 16
    let b3 := (ba.get! (off + 3)).toUInt32 <<< 24
    b0 ||| b1 ||| b2 ||| b3
  else
    0

@[inline]
def readUInt64LE (ba : ByteArray) (off : Nat) : UInt64 :=
  if off + 8 ≤ ba.size then
    let b0 := (ba.get! off).toUInt64
    let b1 := (ba.get! (off + 1)).toUInt64 <<< 8
    let b2 := (ba.get! (off + 2)).toUInt64 <<< 16
    let b3 := (ba.get! (off + 3)).toUInt64 <<< 24
    let b4 := (ba.get! (off + 4)).toUInt64 <<< 32
    let b5 := (ba.get! (off + 5)).toUInt64 <<< 40
    let b6 := (ba.get! (off + 6)).toUInt64 <<< 48
    let b7 := (ba.get! (off + 7)).toUInt64 <<< 56
    b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5 ||| b6 ||| b7
  else
    0

/-- Format a 64-bit unsigned integer as a 16-character lowercase hex string. -/
def uint64ToHex16 (v : UInt64) : String := Id.run do
  let hexChars := "0123456789abcdef".toUTF8
  let mut out := ByteArray.emptyWithCapacity 16
  for i in [0:16] do
    let shift := ((15 - i) * 4).toUInt64
    let nib := ((v >>> shift) &&& 0xF).toNat
    out := out.push (hexChars.get! nib)
  return String.fromUTF8! out

/-- Parse a 16-character hex string back into `UInt64` (returns `0` if empty or invalid). -/
def hexToUInt64 (s : String) : UInt64 := Id.run do
  let bytes := s.trimAscii.toString.toUTF8
  if bytes.isEmpty then return 0
  let mut acc : UInt64 := 0
  for i in [0:bytes.size] do
    let c := bytes.get! i
    let d : UInt64 :=
      if 48 ≤ c && c ≤ 57 then (c - 48).toUInt64
      else if 97 ≤ c && c ≤ 102 then (c - 97 + 10).toUInt64
      else if 65 ≤ c && c ≤ 70 then (c - 65 + 10).toUInt64
      else 0
    acc := (acc <<< 4) ||| d
  return acc

/-! ## WAL Frame Encoding & Verified Decoding (`leansys_verify_wal_frame`) -/

/-- Append one `(key, value)` WAL frame directly into `out` (single buffer, no intermediate payload copy).
    Layout: `magic : UInt32`, `payloadLen : UInt32`, `xxh64(payload) : UInt64`, `keyLen : UInt32`, `key`, `val`. -/
@[inline]
def encodeFrame (out : ByteArray) (keyBytes : ByteArray) (val : ByteSlice) : ByteArray := Id.run do
  let keyLen := keyBytes.size
  let payloadLen := 4 + keyLen + val.len
  let base := out.size
  let mut f := pushUInt32LE out walMagic
  f := pushUInt32LE f payloadLen.toUInt32
  f := pushUInt64LE f 0
  f := pushUInt32LE f keyLen.toUInt32
  f := keyBytes.copySlice 0 f f.size keyLen false
  f := val.ba.copySlice val.off f f.size val.len false
  let csum := xxh64Slice { ba := f, off := base + 16, len := payloadLen }
  for i in [0:8] do
    f := f.set! (base + 8 + i) ((csum >>> (8 * i).toUInt64) &&& 0xFF).toUInt8
  return f

/-- Encode a `(key, value)` pair into a 16-byte header + payload WAL frame. -/
@[inline]
def encodeWalKVFrame (key : String) (val : ByteSlice) : ByteArray :=
  let kb := key.toUTF8
  encodeFrame (ByteArray.emptyWithCapacity (20 + kb.size + val.len)) kb val

/-- Verify the WAL frame at `offset` via `Spec.verifyWalFrame`, hashing the payload in place.
    Returns `(payloadOff, payloadLen, keyLen)` on success. -/
@[inline]
def verifyFrameAt (buf : ByteArray) (offset : Nat) : Option (Nat × Nat × Nat) :=
  if offset + 20 > buf.size then none else
  let magic := readUInt32LE buf offset
  let payloadLen := readUInt32LE buf (offset + 4)
  let expectedHash := readUInt64LE buf (offset + 8)
  let pOff := offset + 16
  let avail := Nat.min payloadLen.toNat (buf.size - pOff)
  let computed := xxh64Slice { ba := buf, off := pOff, len := avail }
  if verifyWalFrame magic payloadLen avail.toUInt64 expectedHash computed != 1 || avail < 4 then none else
  let keyLen := (readUInt32LE buf pOff).toNat
  if 4 + keyLen > avail then none else some (pOff, avail, keyLen)

/-- Decode a single WAL frame at `offset` in `buf`, gated by `Spec.verifyWalFrame`.
    Returns `some (key, valSlice, nextOffset)` on valid frame, or `none` on EOF / torn tail / checksum mismatch. -/
def decodeWalFrameAt (buf : ByteArray) (offset : Nat) : Option (String × ByteSlice × Nat) := do
  let (pOff, avail, keyLen) ← verifyFrameAt buf offset
  let key ← String.fromUTF8? (buf.extract (pOff + 4) (pOff + 4 + keyLen))
  some (key, { ba := buf, off := pOff + 4 + keyLen, len := avail - 4 - keyLen }, pOff + avail)

/-- Replay all valid prefix frames from a raw WAL buffer, stopping cleanly at any torn tail. -/
def replayWalBuffer (buf : ByteArray) : Std.HashMap String ByteArray × Nat × Bool := Id.run do
  let mut kv : Std.HashMap String ByteArray := {}
  let mut offset : Nat := 0
  let mut validFrames : Nat := 0
  let mut hadTornTail : Bool := false
  while offset < buf.size do
    match decodeWalFrameAt buf offset with
    | some (k, vSlice, nextOff) =>
      kv := kv.insert k vSlice.toByteArray
      offset := nextOff
      validFrames := validFrames + 1
    | none =>
      hadTornTail := true
      break
  return (kv, validFrames, hadTornTail)

/-! ## Persistent Store Handle (`LeanSys.Store.Handle`) -/

/-- Persistent WAL + Hardlinked CAS Store state. -/
structure Handle where
  rootDir     : String
  walPath     : String
  lockPath    : String
  casDir      : String
  kv          : Std.HashMap String ByteArray
  framesCount : Nat
  tornCleaned : Bool

/-- Ensure directory hierarchy exists (`rootDir` and `casDir`). -/
def ensureStoreDirs (rootDir : String) : IO ( String × String × String ) := do
  let pRoot : System.FilePath := rootDir
  let pCas  : System.FilePath := pRoot / "cas"
  IO.FS.createDirAll pCas
  let walPath := (pRoot / "state.wal").toString
  let lockPath := (pRoot / "state.lock").toString
  return (walPath, lockPath, pCas.toString)

/-- Open a `LeanSys.Store` at `rootDir`, replaying committed WAL frames and truncating any torn tail. -/
def openStore (rootDir : String) : IO (SysResult Handle) := do
  let (walPath, lockPath, casDir) ← ensureStoreDirs rootDir
  withDirLock lockPath false fun _ => do
    match ← openFd walPath 1 with
    | .error e => pure (.error e)
    | .ok fd =>
      let rawBuf ← try
        preadByteArray fd 0 67108864
      finally
        discard <| closeFd fd
      let (kv, framesCount, hadTornTail) := replayWalBuffer rawBuf
      let h : Handle := {
        rootDir := rootDir
        walPath := walPath
        lockPath := lockPath
        casDir := casDir
        kv := kv
        framesCount := framesCount
        tornCleaned := hadTornTail
      }
      if hadTornTail then
        let tmpPath := walPath ++ ".recover.tmp"
        let mut cleanBytes := ByteArray.empty
        for (k, v) in kv.toList do
          cleanBytes := cleanBytes ++ encodeWalKVFrame k (ByteSlice.ofByteArray v)
        match ← withFd tmpPath 4 (fun wfd => writeAll wfd cleanBytes true) with
        | .error e => pure (.error e)
        | .ok _ =>
          match ← atomicRename tmpPath walPath with
          | .error e => pure (.error e)
          | .ok () => pure (.ok h)
      else
        pure (.ok h)

/-- Append a `(key, val)` frame to the WAL with `O_APPEND` + `fsync` under `flock(LOCK_EX)`. -/
def put (h : Handle) (key : String) (val : ByteSlice) (doSync : Bool := true) : IO (SysResult Handle) := do
  let frame := encodeWalKVFrame key val
  withDirLock h.lockPath false fun _ => do
    match ← withFd h.walPath 2 (fun fd => writeAll fd frame doSync) with
    | .error e => pure (.error e)
    | .ok _ =>
      pure (.ok {
        h with
        kv := h.kv.insert key val.toByteArray
        framesCount := h.framesCount + 1
      })

/-- Convenience wrapper for storing a UTF-8 string value in `Handle`. -/
@[inline]
def putString (h : Handle) (key : String) (val : String) (doSync : Bool := true) : IO (SysResult Handle) :=
  put h key (ByteSlice.ofString val) doSync

/-- Group-commit a batch of `(key, val)` pairs to the WAL in a single `writeAll` + `fsync` syscall under `flock(LOCK_EX)`. -/
def putBatch (h : Handle) (entries : Array (String × ByteSlice)) (doSync : Bool := true) : IO (SysResult Handle) := do
  if entries.isEmpty then return .ok h
  let mut cap := 0
  for (k, v) in entries do
    cap := cap + 20 + k.utf8ByteSize + v.len
  let mut batchBuf := ByteArray.emptyWithCapacity cap
  let mut nextKv := h.kv
  for (k, v) in entries do
    batchBuf := encodeFrame batchBuf k.toUTF8 v
    nextKv := nextKv.insert k v.toByteArray
  withDirLock h.lockPath false fun _ => do
    match ← withFd h.walPath 2 (fun fd => writeAll fd batchBuf doSync) with
    | .error e => pure (.error e)
    | .ok _ =>
      pure (.ok {
        h with
        kv := nextKv
        framesCount := h.framesCount + entries.size
      })

/-- Lookup a value by `key` in the in-memory `Std.HashMap` index in O(1). -/
@[inline]
def get? (h : Handle) (key : String) : Option ByteArray :=
  h.kv.get? key

/-- Lookup a UTF-8 string value by `key`. -/
@[inline]
def getString? (h : Handle) (key : String) : Option String :=
  (h.kv.get? key).map String.fromUTF8!

/-- Atomically compact the WAL in O(N) single-allocation pass by pre-calculating total frame bytes,
    encoding live keys in-place into `state.wal.compact.tmp`, `fsync`ing, and `rename`ing over `state.wal`. -/
def compact (h : Handle) : IO (SysResult Handle) := do
  withDirLock h.lockPath false fun _ => do
    let tmpPath := h.walPath ++ ".compact.tmp"
    let (cap, count) := h.kv.fold (fun (c, n) k v => (c + 20 + k.utf8ByteSize + v.size, n + 1)) (0, 0)
    let compacted := h.kv.fold (fun buf k v => encodeFrame buf k.toUTF8 (ByteSlice.ofByteArray v))
      (ByteArray.emptyWithCapacity cap)
    match ← withFd tmpPath 4 (fun fd => writeAll fd compacted true) with
    | .error e => pure (.error e)
    | .ok _ =>
      match ← atomicRename tmpPath h.walPath with
      | .error e => pure (.error e)
      | .ok () =>
        pure (.ok { h with framesCount := count })

/-! ## Content-Addressable Storage (`casPut` / `casMaterialize`) -/

/-- Check if a CAS digest string contains any path separator or traversal character (`/` or `\`). -/
def hasPathTraversal (s : String) : UInt8 := Id.run do
  let bytes := s.toUTF8
  for i in [0:bytes.size] do
    let b := bytes.get! i
    if b == 47 || b == 92 || b == 0 then
      return (1 : UInt8)
  if (s.splitOn "..").length > 1 then return (1 : UInt8)
  return (0 : UInt8)

/-- Write a `ByteSlice` into the content-addressable store, gated by `leansys_verify_cas_digest`.
    Returns the 16-char hex digest key. -/
def casPut (h : Handle) (payload : ByteSlice) : IO (SysResult String) := do
  let digest := xxh64Slice payload
  let hexKey := uint64ToHex16 digest
  if verifyCasDigest digest digest (hasPathTraversal hexKey) != 1 then
    return .error .einval
  let dstPath := (System.FilePath.mk h.casDir / hexKey).toString
  if ← (System.FilePath.mk dstPath).pathExists then
    return .ok hexKey
  let tmpPath := dstPath ++ ".tmp"
  match ← withFd tmpPath 4 (fun fd => writeSliceAll fd payload true) with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← atomicRename tmpPath dstPath with
    | .error e => pure (.error e)
    | .ok () => pure (.ok hexKey)

/-- Materialize a CAS object identified by `hexKey` to `targetPath` via zero-copy POSIX hardlink (`link(2)`),
    verifying digest integrity through `leansys_verify_cas_digest`. -/
def casMaterialize (h : Handle) (hexKey : String) (targetPath : String) : IO (SysResult Unit) := do
  let cleanKey := match hexKey.splitOn ":" with
    | [_, rest] => rest
    | _ => hexKey
  let expectedDigest := hexToUInt64 cleanKey
  let pathSep := hasPathTraversal cleanKey
  let casPath := (System.FilePath.mk h.casDir / cleanKey).toString
  match ← withFd casPath 0 (fun fd => do
    let bytes ← preadByteArray fd 0 67108864
    pure (.ok bytes)) with
  | .error e => pure (.error e)
  | .ok bytes =>
    let computedDigest := xxh64Slice (ByteSlice.ofByteArray bytes)
    if verifyCasDigest expectedDigest computedDigest pathSep != 1 then
      pure (.error .einval)
    else
      hardLinkReplace casPath targetPath

end LeanSys.Store
