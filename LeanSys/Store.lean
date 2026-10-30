/-
  LeanSys.Store: Crash-Atomic Append-Only WAL, In-Memory KV Index, and Immutable CAS
  (`0 import Lean`, `0 sorryAx`)
  - 16-byte WAL frame header: `magic : UInt32 := 0x4C535953 ("LSYS")`, `payloadLen : UInt32`,
    `xxh64(payload) : UInt64`, followed by `payload : ByteArray` (`keyLen : UInt32` + `key` + `val`).
  - Streaming bounded-memory `pread` WAL replay (`replayWalFd`) handles logs arbitrarily larger than 64 MiB:
    truncates incomplete EOF torn tails, while failing closed (`.error .eio`) on mid-log corruption
    or invalid headers/checksums where full frame bytes were written.
  - Atomic compaction (`Store.compact`) writes a fresh WAL to `.tmp`, `fsync`s, and atomically `rename`s.
  - Content-Addressable Store (`Store.casPut`, `Store.casMaterialize`) seals CAS blobs read-only (`0444`)
    and materializes independent writable (`0644`) copies verified via `leansys_verify_cas_digest`,
    preventing post-materialization caller writes from corrupting CAS objects.
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Auth
import Std.Data.HashMap

namespace LeanSys.Store

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Auth (Digest256 Sha256Stream)

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

/-- Parse a exact 16-character hex string into `Option UInt64`. -/
def parseHex16? (s : String) : Option UInt64 := Id.run do
  let bytes := s.trimAscii.toString.toUTF8
  if bytes.size != 16 then return none
  let mut acc : UInt64 := 0
  for i in [0:16] do
    let c := bytes.get! i
    if 48 ≤ c && c ≤ 57 then
      acc := (acc <<< 4) ||| (c - 48).toUInt64
    else if 97 ≤ c && c ≤ 102 then
      acc := (acc <<< 4) ||| (c - 97 + 10).toUInt64
    else if 65 ≤ c && c ≤ 70 then
      acc := (acc <<< 4) ||| (c - 65 + 10).toUInt64
    else
      return none
  return some acc

/-- Parse a 16-character hex string back into `UInt64` (returns `0` if empty or invalid). -/
def hexToUInt64 (s : String) : UInt64 :=
  (parseHex16? s).getD 0

/-! ## WAL Frame Encoding & Verified Streaming Decoding (`leansys_verify_wal_frame`) -/

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

/-- Outcome of inspecting a single WAL frame at `offset`. -/
inductive WalFrameStep where
  | ok (key : String) (val : ByteSlice) (nextOffset : Nat)
  | needMore
  | tornTail
  | corrupt
  deriving Inhabited

/-- Classify and decode one WAL frame at `offset` in `buf` (`isFinalChunk = true` when `buf` reaches file EOF).
    - Incomplete trailing header or payload at EOF (`isFinalChunk = true`) with valid header bounds -> `.tornTail`
    - Invalid magic, oversized/sub-4-byte `payloadLen`, checksum mismatch with full bytes present,
      bad `keyLen`, or invalid UTF-8 key -> `.corrupt` (fail-closed)
    - Incomplete frame before EOF (`isFinalChunk = false`) -> `.needMore` -/
def stepWalFrameAt (buf : ByteArray) (offset : Nat) (isFinalChunk : Bool) : WalFrameStep :=
  let rem := buf.size - offset
  if rem == 0 then
    .needMore
  else if rem < 16 then
    if isFinalChunk then
      let prefixOk := Id.run do
        let magicBytes : Array UInt8 := #[0x53, 0x59, 0x53, 0x4C]
        let nCheck := Nat.min rem 4
        for i in [0:nCheck] do
          if buf.get! (offset + i) != magicBytes[i]! then
            return false
        return true
      if prefixOk then .tornTail else .corrupt
    else
      .needMore
  else
    let magic := readUInt32LE buf offset
    let payloadLen := readUInt32LE buf (offset + 4)
    let pLenNat := payloadLen.toNat
    if magic != walMagic || payloadLen < 4 || payloadLen > walMaxPayload then
      .corrupt
    else if rem < 16 + pLenNat then
      if isFinalChunk then .tornTail else .needMore
    else
      let expectedHash := readUInt64LE buf (offset + 8)
      let pOff := offset + 16
      let computed := xxh64Slice { ba := buf, off := pOff, len := pLenNat }
      if verifyWalFrame magic payloadLen pLenNat.toUInt64 expectedHash computed != 1 then
        .corrupt
      else
        let keyLen := (readUInt32LE buf pOff).toNat
        if 4 + keyLen > pLenNat then
          .corrupt
        else
          match String.fromUTF8? (buf.extract (pOff + 4) (pOff + 4 + keyLen)) with
          | none => .corrupt
          | some key =>
            .ok key { ba := buf, off := pOff + 4 + keyLen, len := pLenNat - 4 - keyLen } (pOff + pLenNat)

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

/-- Pure in-memory WAL buffer replay with fail-closed mid-buffer corruption detection.
    Returns `.ok (kv, validFrames, hadTornTail, validPrefixBytes)` or `.error .eio` on corrupt frames. -/
def replayWalBufferChecked (buf : ByteArray) : SysResult (Std.HashMap String ByteArray × Nat × Bool × Nat) := Id.run do
  let mut kv : Std.HashMap String ByteArray := {}
  let mut offset : Nat := 0
  let mut validFrames : Nat := 0
  let mut hadTornTail : Bool := false
  while offset < buf.size do
    match stepWalFrameAt buf offset true with
    | .ok k vSlice nextOff =>
      kv := kv.insert k vSlice.toByteArray
      offset := nextOff
      validFrames := validFrames + 1
    | .tornTail =>
      hadTornTail := true
      break
    | .corrupt =>
      return .error .eio
    | .needMore =>
      break
  return .ok (kv, validFrames, hadTornTail, offset)

/-- Legacy pure helper: replay valid prefix frames from a raw WAL buffer. -/
def replayWalBuffer (buf : ByteArray) : Std.HashMap String ByteArray × Nat × Bool :=
  match replayWalBufferChecked buf with
  | .ok (kv, frames, torn, _) => (kv, frames, torn)
  | .error _ => ({}, 0, true)

/-- Default streaming `pread` window size for WAL replay (4 MiB; dynamically grows up to 16 MiB + 16 B for max frames). -/
@[inline] def defaultWalChunkBytes : Nat := 4194304

/-- Stream-replay a WAL file descriptor across known byte extent `fileSize` using bounded `readChunk` windows.
    - Truncates an incomplete EOF torn tail cleanly (`hadTornTail = true`, returning `validPrefixBytes`).
    - Fails closed with `.error .eio` on any premature empty read before `fileSize` (`fileOff < fileSize`),
      corrupt mid-log frame, bad magic, or payload checksum mismatch (never misclassifying a transient
      read error as an EOF torn tail that would truncate committed frames). -/
def replayWalReader (fileSize : UInt64) (readChunk : UInt64 → Nat → IO ByteArray)
    (chunkBytes : Nat := defaultWalChunkBytes) :
    IO (SysResult (Std.HashMap String ByteArray × Nat × Bool × UInt64)) := do
  if fileSize == 0 then
    return .ok ({}, 0, false, 0)
  let stepChunk := Nat.max 65536 chunkBytes
  let mut kv : Std.HashMap String ByteArray := {}
  let mut validFrames : Nat := 0
  let mut fileOff : UInt64 := 0
  let mut carry := ByteArray.empty
  let mut hadTornTail := false
  let mut validPrefixBytes : UInt64 := 0
  let mut atEof := false
  while !atEof || carry.size > 0 do
    if !atEof && carry.size < 16 + walMaxPayload.toNat then
      if fileOff >= fileSize then
        atEof := true
      else
        let remFile := (fileSize - fileOff).toNat
        let toRead := Nat.min remFile stepChunk
        let chunk ← readChunk fileOff toRead
        if chunk.isEmpty then
          return .error .eio
        else
          fileOff := fileOff + chunk.size.toUInt64
          if fileOff >= fileSize then
            atEof := true
          carry := if carry.isEmpty then chunk else carry ++ chunk
    let mut localOff : Nat := 0
    let mut needMoreData := false
    while localOff < carry.size && !needMoreData && !hadTornTail do
      match stepWalFrameAt carry localOff atEof with
      | .ok k vSlice nextOff =>
        let consumed := nextOff - localOff
        kv := kv.insert k vSlice.toByteArray
        localOff := nextOff
        validFrames := validFrames + 1
        validPrefixBytes := validPrefixBytes + consumed.toUInt64
      | .needMore =>
        if atEof then
          hadTornTail := true
        else
          needMoreData := true
      | .tornTail =>
        hadTornTail := true
      | .corrupt =>
        return .error .eio
    if hadTornTail then
      break
    if localOff > 0 then
      carry := if localOff >= carry.size then ByteArray.empty else carry.extract localOff carry.size
    if atEof && carry.isEmpty then
      break
    if needMoreData && !atEof && carry.size >= 16 + walMaxPayload.toNat then
      return .error .eio
  return .ok (kv, validFrames, hadTornTail, validPrefixBytes)

/-- Stream-replay a WAL file descriptor of arbitrary size (`> 64 MiB` supported) using bounded `pread` windows.
    - Truncates an incomplete EOF torn tail cleanly (`hadTornTail = true`, returning `validPrefixBytes`).
    - Fails closed with `.error .eio` on any premature empty read before `fstatSize` or mid-log frame corruption. -/
def replayWalFd (fd : Fd) (chunkBytes : Nat := defaultWalChunkBytes) :
    IO (SysResult (Std.HashMap String ByteArray × Nat × Bool × UInt64)) := do
  match ← fstatSize fd with
  | .error e => return .error e
  | .ok fileSize =>
    replayWalReader fileSize (preadByteArray fd) chunkBytes

/-! ## Persistent Store Handle (`LeanSys.Store.Handle`) -/

/-- Persistent WAL + Immutable CAS Store state. -/
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

/-- Open a `LeanSys.Store` at `rootDir` using streaming `pread` WAL replay (`chunkBytes` window):
    - Supports WAL files arbitrarily larger than 64 MiB.
    - Truncates incomplete EOF torn tails in place via `ftruncate` + `fsync`.
    - Fails closed (`.error .eio`) on mid-log frame corruption. -/
def openStoreWithChunk (rootDir : String) (chunkBytes : Nat := defaultWalChunkBytes) : IO (SysResult Handle) := do
  let (walPath, lockPath, casDir) ← ensureStoreDirs rootDir
  withDirLock lockPath false fun _ => do
    match ← openFd walPath 1 with
    | .error e => pure (.error e)
    | .ok fd =>
      let replayRes ← try
        replayWalFd fd chunkBytes
      finally
        discard <| closeFd fd
      match replayRes with
      | .error e => pure (.error e)
      | .ok (kv, framesCount, hadTornTail, validPrefixBytes) =>
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
          match ← withFd walPath 5 (fun wfd => do
            match ← ftruncateFd wfd validPrefixBytes.toNat with
            | .error e => pure (.error e)
            | .ok () =>
              match ← writeAll wfd ByteArray.empty true with
              | .error e => pure (.error e)
              | .ok _ => pure (.ok ())) with
          | .error e => pure (.error e)
          | .ok () => pure (.ok h)
        else
          pure (.ok h)

/-- Open a `LeanSys.Store` at `rootDir`, replaying committed WAL frames and truncating any EOF torn tail. -/
@[inline]
def openStore (rootDir : String) : IO (SysResult Handle) :=
  openStoreWithChunk rootDir defaultWalChunkBytes

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

/-! ## Immutable Content-Addressable Storage (`casPut` / `casGet` / `casMaterialize`) -/

/-- Check if a CAS digest string contains any path separator or traversal character (`/` or `\`). -/
def hasPathTraversal (s : String) : UInt8 := Id.run do
  let bytes := s.toUTF8
  for i in [0:bytes.size] do
    let b := bytes.get! i
    if b == 47 || b == 92 || b == 0 then
      return (1 : UInt8)
  if (s.splitOn "..").length > 1 then return (1 : UInt8)
  return (0 : UInt8)

/-- Read and digest-verify an entire CAS blob from `casPath` using exact `fstatSize`. -/
private def readVerifiedCasBlob (casPath : String) (expectedDigest : UInt64) (pathSep : UInt8) :
    IO (SysResult ByteArray) := do
  if pathSep != 0 || expectedDigest == 0 then
    return .error .einval
  match ← withFd casPath 0 (fun fd => do
    match ← fstatSize fd with
    | .error e => pure (.error e)
    | .ok sz =>
      let bytes ← preadByteArray fd 0 sz.toNat
      if bytes.size != sz.toNat then
        pure (.error .eio)
      else
        pure (.ok bytes)) with
  | .error e => pure (.error e)
  | .ok bytes =>
    let computedDigest := xxh64Slice (ByteSlice.ofByteArray bytes)
    if verifyCasDigest expectedDigest computedDigest pathSep != 1 then
      pure (.error .einval)
    else
      pure (.ok bytes)

/-- Write a `ByteSlice` into the content-addressable store, gated by `leansys_verify_cas_digest`.
    Seals the stored blob read-only (`chmod 0444`) before atomic `rename` and verifies existing blobs
    before deduplicating. Returns the 16-char hex digest key. -/
def casPut (h : Handle) (payload : ByteSlice) : IO (SysResult String) := do
  let digest := xxh64Slice payload
  let hexKey := uint64ToHex16 digest
  let pathSep := hasPathTraversal hexKey
  if verifyCasDigest digest digest pathSep != 1 then
    return .error .einval
  let dstPath := (System.FilePath.mk h.casDir / hexKey).toString
  if ← (System.FilePath.mk dstPath).pathExists then
    match ← readVerifiedCasBlob dstPath digest pathSep with
    | .ok _ =>
      discard <| chmodReadOnly dstPath
      return .ok hexKey
    | .error _ =>
      pure ()
  let nonce ← IO.monoNanosNow
  let tmpPath := s!"{dstPath}.{nonce}.tmp"
  match ← withFd tmpPath 4 (fun fd => writeSliceAll fd payload true) (exclusive := 2) with
  | .error e => pure (.error e)
  | .ok _ =>
    match ← chmodReadOnly tmpPath with
    | .error e => pure (.error e)
    | .ok () =>
      match ← atomicRename tmpPath dstPath with
      | .error e => pure (.error e)
      | .ok () => pure (.ok hexKey)

/-- Read and verify a CAS object by `hexKey` into memory via `leansys_verify_cas_digest`. -/
def casGet (h : Handle) (hexKey : String) : IO (SysResult ByteArray) := do
  let cleanKey := match hexKey.splitOn ":" with
    | [_, rest] => rest
    | _ => hexKey
  let pathSep := hasPathTraversal cleanKey
  let some expectedDigest := parseHex16? cleanKey
    | return .error .einval
  let casPath := (System.FilePath.mk h.casDir / cleanKey).toString
  readVerifiedCasBlob casPath expectedDigest pathSep

/-- Materialize a CAS object identified by `hexKey` to `targetPath` as an independent writable (`0644`) file
    via atomic temp-write + `fsync` + `rename`, after verifying digest integrity through `leansys_verify_cas_digest`.
    Mutating `targetPath` never mutates the read-only (`0444`) CAS blob. -/
def casMaterialize (h : Handle) (hexKey : String) (targetPath : String) : IO (SysResult Unit) := do
  match ← casGet h hexKey with
  | .error e => pure (.error e)
  | .ok bytes =>
    let nonce ← IO.monoNanosNow
    let tmpTarget := s!"{targetPath}.{nonce}.cas.tmp"
    match ← withFd tmpTarget 4 (fun fd => writeAll fd bytes true) (exclusive := 2) with
    | .error e => pure (.error e)
    | .ok _ => atomicRename tmpTarget targetPath


/-! ## Streaming 256-Bit Cryptographic CAS & CoW Reflink Materialization (`casPutStream256`, `casMaterializeReflink`) -/

/-- Cryptographic 256-bit CAS algorithm selector (`sha256` standard FIPS 180-4, `keyed256` domain-separated 256-bit stream). -/
inductive CasAlgo256 where
  | sha256
  | keyed256 (domainTag : UInt32 := 0x424C4B33)
  deriving Repr, DecidableEq, Inhabited

/-- Materialization receipt indicating whether CoW reflink (`FICLONE` / `clonefile`) or caller-authorized copy ran. -/
inductive ReflinkOutcome where
  | reflinked
  | copiedFallback
  deriving Repr, DecidableEq

@[inline]
private def initCasStream (algo : CasAlgo256) : Sha256Stream :=
  match algo with
  | .sha256 => Sha256Stream.init
  | .keyed256 tag => Sha256Stream.initDomain tag

/-- Stream-verify an open file at `path` in bounded `chunkBytes` (default `1 MiB`) `pread` windows without loading
    the full blob into RAM, returning its 256-bit `Digest256`. -/
def computeFileDigest256 (path : String) (algo : CasAlgo256 := .sha256) (chunkBytes : Nat := 1048576) : IO (SysResult Digest256) := do
  let step := Nat.max 4096 (Nat.min chunkBytes 4194304)
  withFd path 0 fun fd => do
    match ← fstatSize fd with
    | .error e => pure (.error e)
    | .ok totalSz =>
      let mut st := initCasStream algo
      let mut off : UInt64 := 0
      while off < totalSz do
        let rem := (totalSz - off).toNat
        let want := Nat.min step rem
        let chunk ← preadByteArray fd off want
        if chunk.size == 0 then
          return .error .eio
        st := st.updateBytes chunk
        off := off + chunk.size.toUInt64
      pure (.ok st.finalizeDigest256)

/-- Verify a 256-bit CAS blob on disk via bounded `pread` streaming + `leansys_verify_cas_digest256` (constant-time 4-limb XOR). -/
def verifyCasFile256 (casPath : String) (expected : Digest256) (pathSep : UInt8)
    (algo : CasAlgo256 := .sha256) (chunkBytes : Nat := 1048576) : IO (SysResult Unit) := do
  if pathSep != 0 then
    return .error .einval
  match ← computeFileDigest256 casPath algo chunkBytes with
  | .error e => pure (.error e)
  | .ok computed =>
    if verifyCasDigest256 expected.w0 expected.w1 expected.w2 expected.w3
         computed.w0 computed.w1 computed.w2 computed.w3 pathSep == 1 then
      pure (.ok ())
    else
      pure (.error .einval)

/-- Stream-ingest `srcFilePath` into the immutable `0444` CAS using bounded `1–4 MiB` `pread` chunks,
    returning `"sha256:<64-hex>"` (or `"blake256:<64-hex>"`), gated by `leansys_verify_cas_digest256`. -/
def casPutFile256 (h : Handle) (srcFilePath : String) (algo : CasAlgo256 := .sha256)
    (chunkBytes : Nat := 1048576) : IO (SysResult String) := do
  let step := Nat.max 4096 (Nat.min chunkBytes 4194304)
  let nonce ← IO.monoNanosNow
  let tmpPath := (System.FilePath.mk h.casDir / s!"ingest.{nonce}.tmp").toString
  let res ← withFd srcFilePath 0 fun sfd => do
    match ← fstatSize sfd with
    | .error e => pure (.error e)
    | .ok totalSz =>
      withFd tmpPath 4 (exclusive := 2) fun dfd => do
        let mut st := initCasStream algo
        let mut off : UInt64 := 0
        while off < totalSz do
          let want := Nat.min step (totalSz - off).toNat
          let chunk ← preadByteArray sfd off want
          if chunk.size == 0 then
            return .error .eio
          st := st.updateBytes chunk
          match ← writeAll dfd chunk false with
          | .error e => return .error e
          | .ok _ => off := off + chunk.size.toUInt64
        match ← writeAll dfd ByteArray.empty true with
        | .error e => pure (.error e)
        | .ok _ => pure (.ok st.finalizeDigest256)
  match res with
  | .error e =>
    discard <| unlinkFile tmpPath
    return .error e
  | .ok dig =>
    let hex64 := dig.toHexLower
    let pathSep := hasPathTraversal hex64
    if verifyCasDigest256 dig.w0 dig.w1 dig.w2 dig.w3 dig.w0 dig.w1 dig.w2 dig.w3 pathSep != 1 then
      discard <| unlinkFile tmpPath
      return .error .einval
    let prefixTag := match algo with | .sha256 => "sha256:" | .keyed256 _ => "blake256:"
    let dstPath := (System.FilePath.mk h.casDir / hex64).toString
    if ← (System.FilePath.mk dstPath).pathExists then
      match ← verifyCasFile256 dstPath dig pathSep algo chunkBytes with
      | .ok () =>
        discard <| unlinkFile tmpPath
        discard <| chmodReadOnly dstPath
        return .ok (prefixTag ++ hex64)
      | .error _ => pure ()
    match ← chmodReadOnly tmpPath with
    | .error e =>
      discard <| unlinkFile tmpPath
      return .error e
    | .ok () =>
      match ← atomicRename tmpPath dstPath with
      | .error e =>
        discard <| unlinkFile tmpPath
        return .error e
      | .ok () =>
        return .ok (prefixTag ++ hex64)

/-- Put a `ByteSource` (`ByteSlice` or `BorrowedSlice`) into the 256-bit CAS (`"sha256:<64-hex>"`). -/
def casPut256 (h : Handle) (src : ByteSource) (algo : CasAlgo256 := .sha256) : IO (SysResult String) := do
  let st := (initCasStream algo).updateSource src
  let dig := st.finalizeDigest256
  let hex64 := dig.toHexLower
  let pathSep := hasPathTraversal hex64
  if verifyCasDigest256 dig.w0 dig.w1 dig.w2 dig.w3 dig.w0 dig.w1 dig.w2 dig.w3 pathSep != 1 then
    return .error .einval
  let prefixTag := match algo with | .sha256 => "sha256:" | .keyed256 _ => "blake256:"
  let dstPath := (System.FilePath.mk h.casDir / hex64).toString
  if ← (System.FilePath.mk dstPath).pathExists then
    match ← verifyCasFile256 dstPath dig pathSep algo with
    | .ok () =>
      discard <| chmodReadOnly dstPath
      return .ok (prefixTag ++ hex64)
    | .error _ => pure ()
  let nonce ← IO.monoNanosNow
  let tmpPath := s!"{dstPath}.{nonce}.256.tmp"
  let bytes := src.toByteArray
  match ← withFd tmpPath 4 (fun fd => writeAll fd bytes true) (exclusive := 2) with
  | .error e =>
    discard <| unlinkFile tmpPath
    return .error e
  | .ok _ =>
    match ← chmodReadOnly tmpPath with
    | .error e =>
      discard <| unlinkFile tmpPath
      return .error e
    | .ok () =>
      match ← atomicRename tmpPath dstPath with
      | .error e =>
        discard <| unlinkFile tmpPath
        return .error e
      | .ok () => return .ok (prefixTag ++ hex64)

/-- Verify and read a 256-bit CAS object (`"sha256:<64-hex>"` or raw 64-char hex) via `leansys_verify_cas_digest256`. -/
def casGet256 (h : Handle) (key : String) : IO (SysResult ByteArray) := do
  let (algo, cleanHex) := match key.splitOn ":" with
    | ["blake256", rest] => (CasAlgo256.keyed256, rest)
    | [_, rest] => (CasAlgo256.sha256, rest)
    | _ => (CasAlgo256.sha256, key)
  let pathSep := hasPathTraversal cleanHex
  let some expected := Digest256.ofHex? cleanHex
    | return .error .einval
  let casPath := (System.FilePath.mk h.casDir / cleanHex).toString
  match ← verifyCasFile256 casPath expected pathSep algo with
  | .error e => pure (.error e)
  | .ok () =>
    withFd casPath 0 fun fd => do
      match ← fstatSize fd with
      | .error e => pure (.error e)
      | .ok sz => preadByteArray fd 0 sz.toNat >>= (pure ∘ .ok)

/-- Stream-copy `srcPath` to `tmpTarget` in `1 MiB` `pread` chunks with `0644` writable mode + `fsync`. -/
private def streamCopyWritable (srcPath tmpTarget : String) (chunkBytes : Nat := 1048576) : IO (SysResult Unit) := do
  let step := Nat.max 4096 (Nat.min chunkBytes 4194304)
  withFd srcPath 0 fun sfd => do
    match ← fstatSize sfd with
    | .error e => pure (.error e)
    | .ok totalSz =>
      withFd tmpTarget 4 (exclusive := 2) fun dfd => do
        let mut off : UInt64 := 0
        while off < totalSz do
          let want := Nat.min step (totalSz - off).toNat
          let chunk ← preadByteArray sfd off want
          if chunk.size == 0 then
            return .error .eio
          match ← writeAll dfd chunk false with
          | .error e => return .error e
          | .ok _ => off := off + chunk.size.toUInt64
        match ← writeAll dfd ByteArray.empty true with
        | .error e => pure (.error e)
        | .ok _ => pure (.ok ())

/-- Materialize an immutable `0444` CAS object (`16-hex` 64-bit OR `64-hex` 256-bit key) to `targetPath`
    as an independent writable (`0644`) file via CoW reflink (`FICLONE` / `clonefile`) + atomic `rename`.
    NEVER hardlinks `0444` CAS blobs. When the filesystem returns `.eopnotsupp` or `.exdev`, fails with that
    typed `Errno` unless `allowCopyFallback == true`, in which case it streams `pread` chunks + `fsync` + `rename`. -/
def casMaterializeReflink (h : Handle) (hexKey : String) (targetPath : String)
    (allowCopyFallback : Bool := false) : IO (SysResult ReflinkOutcome) := do
  let (algo256, cleanKey) := match hexKey.splitOn ":" with
    | ["blake256", rest] => (CasAlgo256.keyed256, rest)
    | [_, rest] => (CasAlgo256.sha256, rest)
    | _ => (CasAlgo256.sha256, hexKey)
  let pathSep := hasPathTraversal cleanKey
  let casPath := (System.FilePath.mk h.casDir / cleanKey).toString
  let verified : SysResult Unit ←
    if cleanKey.utf8ByteSize == 64 then
      match Digest256.ofHex? cleanKey with
      | none => pure (.error .einval)
      | some exp256 => verifyCasFile256 casPath exp256 pathSep algo256
    else
      match parseHex16? cleanKey with
      | none => pure (.error .einval)
      | some exp64 =>
        match ← readVerifiedCasBlob casPath exp64 pathSep with
        | .ok _ => pure (.ok ())
        | .error e => pure (.error e)
  match verified with
  | .error e => return .error e
  | .ok () =>
    let nonce ← IO.monoNanosNow
    let tmpTarget := s!"{targetPath}.{nonce}.reflink.tmp"
    match ← reflinkFile casPath tmpTarget with
    | .ok () =>
      match ← atomicRename tmpTarget targetPath with
      | .ok () => return .ok .reflinked
      | .error e =>
        discard <| unlinkFile tmpTarget
        return .error e
    | .error e =>
      discard <| unlinkFile tmpTarget
      if allowCopyFallback && (e == .eopnotsupp || e == .exdev || e == .enosys || e == .einval) then
        match ← streamCopyWritable casPath tmpTarget with
        | .error ce =>
          discard <| unlinkFile tmpTarget
          return .error ce
        | .ok () =>
          match ← atomicRename tmpTarget targetPath with
          | .ok () => return .ok .copiedFallback
          | .error re =>
            discard <| unlinkFile tmpTarget
            return .error re
      else
        return .error e

end LeanSys.Store
