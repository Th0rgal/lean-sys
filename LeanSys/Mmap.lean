/-
  LeanSys.Mmap: True `MAP_SHARED` (`mmap(2)`) Shared-Memory (`/dev/shm`) Circular Ring Buffer
  (`0 import Lean`, `0 sorryAx`)
  - 24-byte shared ring header (`magic = 0x4C524E47 "LRNG"`, `cap : UInt32`, `head : UInt64`, `tail : UInt64`)
  - `ShmRing.init` creates, `ftruncate`s (`24 + effCap`), and writes header via `MAP_SHARED` `mmap`
  - `ShmRing.open` attaches to an existing shared ring (`wr = 5` `O_RDWR`, no `O_TRUNC` / no `O_CREAT`)
    and validates `LRNG` magic, capacity, and cursor invariants without clobbering existing messages
  - Every `push` and `pop?` mutates the circular ring in place via `MAP_SHARED` `mmap` (`mmapReadShared` /
    `mmapWriteShared`), gated by `LeanSys.Spec.verifyRingCursor` (`leansys_verify_ring_cursor`) under `withDirLock`
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Store

namespace LeanSys.Mmap

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Store

/-- Canonical Shared-Memory Ring Magic `0x4C524E47` (`"LRNG"`). -/
@[inline] def ringMagic : UInt32 := 0x4C524E47

/-- Shared-memory circular ring handle backed by `MAP_SHARED` `mmap(2)` on `/dev/shm` (or tmpfs). -/
structure ShmRing where
  path     : String
  lockPath : String
  cap      : UInt32

namespace ShmRing

/-- Encode a 24-byte ring header (`magic`, `cap`, `head`, `tail`). -/
def encodeHeader (cap : UInt32) (head tail : UInt64) : ByteArray :=
  let b := ByteArray.emptyWithCapacity 24
  let b := pushUInt32LE b ringMagic
  let b := pushUInt32LE b cap
  let b := pushUInt64LE b head
  pushUInt64LE b tail

/-- Write `data` into the circular ring payload arena `[24 .. 24 + cap)` at monotonic cursor `cursor`,
    wrapping cleanly around `cap` via at most two `MAP_SHARED` `mmap` writes. -/
private def writeCircularShared (fd : Fd) (cap : Nat) (cursor : UInt64) (data : ByteArray) : IO (SysResult Unit) := do
  if data.isEmpty then
    return .ok ()
  match ← fstatSize fd with
  | .error e => return .error e
  | .ok fsz =>
    if cap.toUInt64.toNat != cap || verifySliceBounds 24 cap.toUInt64 fsz != 1 then
      return .error .einval
    let pos := (cursor.toNat) % cap
    let firstLen := Nat.min data.size (cap - pos)
    let firstChunk := if firstLen == data.size then data else data.extract 0 firstLen
    match ← mmapWriteShared fd (24 + pos) firstChunk with
    | .error e => return .error e
    | .ok _ =>
      if firstLen == data.size then
        return .ok ()
      let secondChunk := data.extract firstLen data.size
      match ← mmapWriteShared fd 24 secondChunk with
      | .error e => return .error e
      | .ok _ => return .ok ()

/-- Read `len` bytes from the circular ring payload arena `[24 .. 24 + cap)` at monotonic cursor `cursor`,
    wrapping cleanly around `cap` via at most two `MAP_SHARED` `mmap` reads. -/
private def readCircularShared (fd : Fd) (cap : Nat) (cursor : UInt64) (len : Nat) : IO (SysResult ByteArray) := do
  if len == 0 then
    return .ok ByteArray.empty
  match ← fstatSize fd with
  | .error e => return .error e
  | .ok fsz =>
    if cap.toUInt64.toNat != cap || verifySliceBounds 24 cap.toUInt64 fsz != 1 then
      return .error .einval
    let pos := (cursor.toNat) % cap
    let firstLen := Nat.min len (cap - pos)
    let firstChunk ← mmapReadShared fd (24 + pos) firstLen
    if firstChunk.size != firstLen then
      return .error .eio
    if firstLen == len then
      return .ok firstChunk
    let remLen := len - firstLen
    let secondChunk ← mmapReadShared fd 24 remLen
    if secondChunk.size != remLen then
      return .error .eio
    return .ok (firstChunk ++ secondChunk)

/-- Read and validate the 24-byte `MAP_SHARED` ring header from an already-open `fd`.
    Validates backing-file extent (`fsz >= 24` before mapping header, and `fsz >= 24 + cap` before payload)
    so empty or truncated backing files fail closed with `.error .einval` without raising `SIGBUS`. -/
private def readHeaderFd (fd : Fd) : IO (SysResult (UInt32 × UInt64 × UInt64)) := do
  match ← fstatSize fd with
  | .error e => pure (.error e)
  | .ok fsz =>
    if verifySliceBounds 0 24 fsz != 1 then
      pure (.error .einval)
    else
      let hdr ← mmapReadShared fd 0 24
      if hdr.size < 24 then
        pure (.error .eio)
      else
        let magic := readUInt32LE hdr 0
        let cap := readUInt32LE hdr 4
        let head := readUInt64LE hdr 8
        let tail := readUInt64LE hdr 16
        if magic != ringMagic || cap < 64 || verifySliceBounds 24 cap.toUInt64 fsz != 1 then
          pure (.error .einval)
        else if verifyRingCursor head tail cap.toUInt64 0 != 1 then
          pure (.error .einval)
        else
          pure (.ok (cap, head, tail))

/-- Read `(magic, cap, head, tail)` from `r.path` via `MAP_SHARED` `mmap(2)`. -/
def readHeader (r : ShmRing) : IO (SysResult (UInt32 × UInt64 × UInt64)) :=
  withFd r.path 0 readHeaderFd

/-- Initialize a fresh `ShmRing` at `path` with data capacity `cap` bytes (rounded up to `>= 64`):
    truncates/resizes backing file to `24 + effCap` via `ftruncate` and writes the `LRNG` header via `MAP_SHARED` `mmap`. -/
def init (path : String) (cap : UInt32 := 65536) : IO (SysResult ShmRing) := do
  let effCap : UInt32 := if cap < 64 then 64 else cap
  let lockPath := path ++ ".lock"
  let hdr := encodeHeader effCap 0 0
  withDirLock lockPath false fun _ => do
    match ← withFd path 4 (fun fd => do
      match ← ftruncateFd fd (24 + effCap.toNat) with
      | .error e => pure (.error e)
      | .ok () =>
        match ← mmapWriteShared fd 0 hdr with
        | .error e => pure (.error e)
        | .ok _ => pure (.ok ())) with
    | .error e => pure (.error e)
    | .ok () => pure (.ok { path := path, lockPath := lockPath, cap := effCap })

/-- Attach to an existing `ShmRing` at `path` without truncating or resetting unread messages (`wr = 5` `O_RDWR`).
    Validates `LRNG` magic, backing file size (`>= 24 + cap`), and `verifyRingCursor` invariant. -/
def «open» (path : String) : IO (SysResult ShmRing) := do
  let lockPath := path ++ ".lock"
  withDirLock lockPath false fun _ => do
    match ← withFd path 5 readHeaderFd with
    | .error e => pure (.error e)
    | .ok (cap, _, _) =>
      pure (.ok { path := path, lockPath := lockPath, cap := cap })

/-- Alias for `ShmRing.open` for callers avoiding French-quote identifiers. -/
@[inline]
def openExisting (path : String) : IO (SysResult ShmRing) :=
  «open» path

/-- Push a `ByteSlice` message into `ShmRing` via in-place `MAP_SHARED` `mmap` writes (no file truncation),
    gated by `leansys_verify_ring_cursor` under `withDirLock`. -/
def push (r : ShmRing) (msg : ByteSlice) : IO (SysResult Unit) := do
  let frameLen : UInt64 := (4 + msg.len).toUInt64
  withDirLock r.lockPath false fun _ => do
    withFd r.path 5 fun fd => do
      match ← readHeaderFd fd with
      | .error e => pure (.error e)
      | .ok (cap, head, tail) =>
        if verifyRingCursor head tail cap.toUInt64 frameLen != 1 then
          pure (.error .enospc)
        else
          let mut frame := ByteArray.emptyWithCapacity (4 + msg.len)
          frame := pushUInt32LE frame msg.len.toUInt32
          if msg.len > 0 then
            frame := msg.ba.copySlice msg.off frame 4 msg.len false
          match ← writeCircularShared fd cap.toNat head frame with
          | .error e => pure (.error e)
          | .ok () =>
            let newHead := head + frameLen
            match ← mmapWriteShared fd 0 (encodeHeader cap newHead tail) with
            | .error e => pure (.error e)
            | .ok _ => pure (.ok ())

/-- Pop the oldest message from `ShmRing` via `MAP_SHARED` `mmap` reads and in-place tail cursor update (`none` if empty). -/
def pop? (r : ShmRing) : IO (SysResult (Option ByteArray)) := do
  withDirLock r.lockPath false fun _ => do
    withFd r.path 5 fun fd => do
      match ← readHeaderFd fd with
      | .error e => pure (.error e)
      | .ok (cap, head, tail) =>
        if head == tail then
          pure (.ok none)
        else if verifyRingCursor head tail cap.toUInt64 0 != 1 then
          pure (.error .einval)
        else
          let unreadLen := (head - tail).toNat
          if unreadLen < 4 then
            pure (.error .eio)
          else
            match ← readCircularShared fd cap.toNat tail 4 with
            | .error e => pure (.error e)
            | .ok lenBytes =>
              let msgLen := (readUInt32LE lenBytes 0).toNat
              let frameLen := 4 + msgLen
              if frameLen > unreadLen then
                pure (.error .eio)
              else
                let newTail := tail + frameLen.toUInt64
                if verifyRingCursor head newTail cap.toUInt64 0 != 1 then
                  pure (.error .einval)
                else
                  match ← readCircularShared fd cap.toNat (tail + 4) msgLen with
                  | .error e => pure (.error e)
                  | .ok payload =>
                    match ← mmapWriteShared fd 0 (encodeHeader cap head newTail) with
                    | .error e => pure (.error e)
                    | .ok _ => pure (.ok (some payload))

/-- Validate a shared-memory seqlock snapshot read across process restarts via `leansys_verify_mmap_seqlock`. -/
@[inline]
def validateSeqlockSnapshot (schemaVersion expectedVersion : UInt32)
    (seqBefore seqAfter writerEpoch minEpoch payloadLen ringCap : UInt64) : Bool :=
  verifyMmapSeqlock mmapSeqlockMagic schemaVersion expectedVersion
    seqBefore seqAfter writerEpoch minEpoch payloadLen ringCap == 1

end ShmRing


/-! ## Persistent Zero-Syscall-Per-Message `MAP_SHARED` Seqlock Ring (`MmapArena`) & Linux `io_uring` -/

/-- Persistent `MAP_SHARED` SPSC ring & seqlock arena mapped once in memory (`0` `open`/`flock`/`munmap` per message).
    40-byte header layout:
    - `[0..4)`: `mmapSeqlockMagic` (`0x4C534D4D` `"LSMM"`)
    - `[4..8)`: `schemaVersion : UInt32` (`1`)
    - `[8..16)`: `seq : UInt64` (even when quiescent, odd during writer update)
    - `[16..24)`: `writerEpoch : UInt64`
    - `[24..32)`: `head : UInt64`
    - `[32..40)`: `tail : UInt64`
    - `[40..40+cap)`: circular payload ring -/
structure MmapArena where
  path          : String
  region        : MmapRegion
  cap           : UInt32
  schemaVersion : UInt32 := 1
  writerEpoch   : UInt64 := 1
  deriving Repr

namespace MmapArena

@[inline] def headerBytes : Nat := 40

private def encodeSeqlockHeader (ver : UInt32) (seq epoch head tail : UInt64) : ByteArray :=
  let b := ByteArray.emptyWithCapacity 40
  let b := pushUInt32LE b mmapSeqlockMagic
  let b := pushUInt32LE b ver
  let b := pushUInt64LE b seq
  let b := pushUInt64LE b epoch
  let b := pushUInt64LE b head
  pushUInt64LE b tail

@[inline]
private def readU32View (v : BorrowedSlice) (off : Nat) : UInt32 :=
  (v.getWord64LE off &&& 0xFFFFFFFF).toUInt32

/-- Create and map a persistent `MAP_SHARED` `MmapArena` of ring capacity `capBytes` (`>= 64`). -/
def create (path : String) (capBytes : UInt32 := 65536) (epoch : UInt64 := 1) : IO (SysResult MmapArena) := do
  let effCap : UInt32 := if capBytes < 64 then 64 else capBytes
  let totalBytes := headerBytes + effCap.toNat
  withFd path 4 fun fd => do
    match ← ftruncateFd fd totalBytes with
    | .error e => pure (.error e)
    | .ok () =>
      match ← mmapMapShared fd totalBytes 0 false with
      | .error e => pure (.error e)
      | .ok reg =>
        let hdr := encodeSeqlockHeader 1 0 epoch 0 0
        match ← mmapRegionWrite reg 0 hdr with
        | .error e =>
          discard <| mmapUnmap reg
          pure (.error e)
        | .ok _ =>
          pure (.ok { path := path, region := reg, cap := effCap, schemaVersion := 1, writerEpoch := epoch })

/-- Attach to an existing `MmapArena` file and map it persistently (`MAP_SHARED`) without truncating. -/
def attach (path : String) (minEpoch : UInt64 := 0) : IO (SysResult MmapArena) := do
  withFd path 5 fun fd => do
    match ← fstatSize fd with
    | .error e => pure (.error e)
    | .ok sz =>
      if sz.toNat < headerBytes + 64 then
        return .error .einval
      let capNat := sz.toNat - headerBytes
      match ← mmapMapShared fd sz.toNat 0 false with
      | .error e => pure (.error e)
      | .ok reg =>
        let some view := reg.view? 0 sz.toNat
          | do discard <| mmapUnmap reg; return .error .einval
        let magic := readU32View view 0
        let ver   := readU32View view 4
        let seq1  := view.getWord64LE 8
        let epoch := view.getWord64LE 16
        let head  := view.getWord64LE 24
        let tail  := view.getWord64LE 32
        let seq2  := view.getWord64LE 8
        if magic != mmapSeqlockMagic ||
           verifyMmapSeqlock magic ver 1 seq1 seq2 epoch minEpoch (head - tail) capNat.toUInt64 != 1 then
          discard <| mmapUnmap reg
          return .error .einval
        pure (.ok { path := path, region := reg, cap := capNat.toUInt32, schemaVersion := ver, writerEpoch := epoch })

/-- Close and `munmap` the persistent `MmapArena`. -/
def close (arena : MmapArena) : IO (SysResult Unit) :=
  mmapUnmap arena.region

/-- Return a zero-copy `BorrowedSlice` over the payload region `[40, 40 + cap)`. -/
@[inline]
def payloadView? (arena : MmapArena) : Option BorrowedSlice :=
  arena.region.view? headerBytes arena.cap.toNat

private def writeRingBytes (reg : MmapRegion) (cap : Nat) (cursor : UInt64) (data : ByteArray) : IO (SysResult Unit) := do
  if data.isEmpty then return .ok ()
  let pos := cursor.toNat % cap
  let firstLen := Nat.min data.size (cap - pos)
  let firstChunk := if firstLen == data.size then data else data.extract 0 firstLen
  match ← mmapRegionWrite reg (headerBytes + pos) firstChunk with
  | .error e => return .error e
  | .ok _ =>
    if firstLen == data.size then return .ok ()
    let rest := data.extract firstLen data.size
    match ← mmapRegionWrite reg headerBytes rest with
    | .error e => return .error e
    | .ok _ => return .ok ()

private def readRingBytes (reg : MmapRegion) (cap : Nat) (cursor : UInt64) (len : Nat) : IO ByteArray := do
  if len == 0 then return ByteArray.empty
  let pos := cursor.toNat % cap
  let firstLen := Nat.min len (cap - pos)
  let c1 ← mmapRegionRead reg (headerBytes + pos) firstLen
  if firstLen == len then
    return c1
  let c2 ← mmapRegionRead reg headerBytes (len - firstLen)
  return c1 ++ c2

/-- Push a length-prefixed frame into the persistent `MmapArena` with zero syscalls (`memcpy` + memory barrier +
    odd/even seqlock fencing gated by `leansys_verify_ring_cursor` and `leansys_verify_mmap_seqlock`). -/
def push (arena : MmapArena) (payload : ByteSlice) : IO (SysResult Bool) := do
  let some hdrView := arena.region.view? 0 headerBytes
    | return .error .einval
  let seq0 := hdrView.getWord64LE 8
  let head := hdrView.getWord64LE 24
  let tail := hdrView.getWord64LE 32
  let frameLen : UInt64 := 4 + payload.len.toUInt64
  if (seq0 &&& 1) != 0 || verifyRingCursor head tail arena.cap.toUInt64 frameLen != 1 then
    return .ok false
  let oddSeq := seq0 + 1
  discard <| mmapRegionWrite arena.region 8 (pushUInt64LE ByteArray.empty oddSeq)
  let lenBytes := pushUInt32LE ByteArray.empty payload.len.toUInt32
  let capNat := arena.cap.toNat
  match ← writeRingBytes arena.region capNat head lenBytes with
  | .error e => return .error e
  | .ok () =>
    match ← writeRingBytes arena.region capNat (head + 4) payload.toByteArray with
    | .error e => return .error e
    | .ok () =>
      let newHead := head + frameLen
      let evenSeq := seq0 + 2
      if verifyMmapSeqlock mmapSeqlockMagic arena.schemaVersion 1 evenSeq evenSeq
           arena.writerEpoch arena.writerEpoch (newHead - tail) arena.cap.toUInt64 != 1 then
        return .error .einval
      discard <| mmapRegionWrite arena.region 24 (pushUInt64LE ByteArray.empty newHead)
      discard <| mmapRegionWrite arena.region 8 (pushUInt64LE ByteArray.empty evenSeq)
      return .ok true

/-- Pop the next frame from the persistent `MmapArena` using lock-free seqlock validation (`leansys_verify_mmap_seqlock`)
    and `leansys_verify_ring_cursor` with zero syscalls. -/
def pop? (arena : MmapArena) (minEpoch : UInt64 := 0) : IO (SysResult (Option ByteArray)) := do
  let some hdrView := arena.region.view? 0 headerBytes
    | return .error .einval
  let magic := readU32View hdrView 0
  let ver   := readU32View hdrView 4
  let seqBefore := hdrView.getWord64LE 8
  let epoch := hdrView.getWord64LE 16
  let head  := hdrView.getWord64LE 24
  let tail  := hdrView.getWord64LE 32
  let seqAfter := hdrView.getWord64LE 8
  if head < tail then return .error .einval
  if verifyMmapSeqlock magic ver 1 seqBefore seqAfter epoch minEpoch (head - tail) arena.cap.toUInt64 != 1 then
    return .error .eagain
  if head == tail then
    return .ok none
  let unread := (head - tail).toNat
  if unread < 4 then return .error .eio
  let capNat := arena.cap.toNat
  let lenBuf ← readRingBytes arena.region capNat tail 4
  let msgLen := (readUInt32LE lenBuf 0).toNat
  let frameLen := 4 + msgLen
  if frameLen > unread then return .error .eio
  let newTail := tail + frameLen.toUInt64
  if verifyRingCursor head newTail arena.cap.toUInt64 0 != 1 then
    return .error .einval
  let body ← readRingBytes arena.region capNat (tail + 4) msgLen
  discard <| mmapRegionWrite arena.region 32 (pushUInt64LE ByteArray.empty newTail)
  return .ok (some body)

end MmapArena

/-! ## Linux `io_uring` Asynchronous SQ/CQ Shared-Memory Ring (`IoUring`) -/

/-- Linux `io_uring` completion queue event (`struct io_uring_cqe`: `user_data : UInt64`, `res : Int32`, `flags : UInt32`). -/
structure IoUringCqe where
  userData : UInt64
  res      : Int32
  flags    : UInt32
  deriving Repr, DecidableEq

/-- Live Linux `io_uring` handle with `MAP_SHARED` SQ ring, CQ ring, and SQE array mappings. -/
structure IoUring where
  ringFd      : Fd
  sqRing      : MmapRegion
  cqRing      : MmapRegion
  sqesRegion  : MmapRegion
  sqEntries   : UInt32
  cqEntries   : UInt32
  sqOffHead   : Nat
  sqOffTail   : Nat
  sqOffMask   : Nat
  sqOffArray  : Nat
  cqOffHead   : Nat
  cqOffTail   : Nat
  cqOffMask   : Nat
  cqOffCqes   : Nat
  singleMmap  : Bool

namespace IoUring

@[inline] def opNop   : UInt8 := 0
@[inline] def opRead  : UInt8 := 22
@[inline] def opWrite : UInt8 := 23

/-- Set up a Linux `io_uring` instance of `entries` SQ slots (power of two `1..4096`), mapping SQ, CQ, and SQEs
    into persistent `MAP_SHARED` regions (`fails closed` with `.enosys` on macOS or kernels with `io_uring` disabled). -/
def setup (entries : UInt32 := 8) : IO (SysResult IoUring) := do
  match ← ioUringSetupRaw entries with
  | .error e => return .error e
  | .ok (rfd, p) =>
    let sqEnt := readUInt32LE p 0
    let cqEnt := readUInt32LE p 4
    let features := readUInt32LE p 20
    let sqHead := (readUInt32LE p 40).toNat
    let sqTail := (readUInt32LE p 44).toNat
    let sqMaskOff := (readUInt32LE p 48).toNat
    let sqArrOff  := (readUInt32LE p 64).toNat
    let cqHead := (readUInt32LE p 80).toNat
    let cqTail := (readUInt32LE p 84).toNat
    let cqMaskOff := (readUInt32LE p 88).toNat
    let cqCqesOff := (readUInt32LE p 100).toNat
    let singleMmap := (features &&& 1) != 0
    let sqRingSz := sqArrOff + sqEnt.toNat * 4
    let cqRingSz := cqCqesOff + cqEnt.toNat * 16
    let mapSz := if singleMmap then Nat.max sqRingSz cqRingSz else sqRingSz
    match ← mmapMapShared rfd mapSz 0 false with
    | .error e =>
      discard <| closeFd rfd
      return .error e
    | .ok sqReg =>
      let cqRegRes : SysResult MmapRegion ←
        if singleMmap then pure (.ok sqReg)
        else mmapMapShared rfd cqRingSz 0x8000000 false
      match cqRegRes with
      | .error e =>
        discard <| mmapUnmap sqReg
        discard <| closeFd rfd
        return .error e
      | .ok cqReg =>
        match ← mmapMapShared rfd (sqEnt.toNat * 64) 0x10000000 false with
        | .error e =>
          if !singleMmap then discard <| mmapUnmap cqReg
          discard <| mmapUnmap sqReg
          discard <| closeFd rfd
          return .error e
        | .ok sqesReg =>
          return .ok {
            ringFd := rfd
            sqRing := sqReg
            cqRing := cqReg
            sqesRegion := sqesReg
            sqEntries := sqEnt
            cqEntries := cqEnt
            sqOffHead := sqHead
            sqOffTail := sqTail
            sqOffMask := sqMaskOff
            sqOffArray := sqArrOff
            cqOffHead := cqHead
            cqOffTail := cqTail
            cqOffMask := cqMaskOff
            cqOffCqes := cqCqesOff
            singleMmap := singleMmap
          }

/-- Tear down `IoUring` mappings and close `ringFd`. -/
def close (ring : IoUring) : IO Unit := do
  discard <| mmapUnmap ring.sqesRegion
  if !ring.singleMmap then
    discard <| mmapUnmap ring.cqRing
  discard <| mmapUnmap ring.sqRing
  discard <| closeFd ring.ringFd

private def buildSqe64 (opcode : UInt8) (fd : Int32) (off addr : UInt64) (len : UInt32) (userData : UInt64) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 64
  b := b.push opcode
  b := b.push 0 -- flags
  b := b.push 0 -- ioprio lo
  b := b.push 0 -- ioprio hi
  b := pushUInt32LE b fd.toUInt32
  b := pushUInt64LE b off
  b := pushUInt64LE b addr
  b := pushUInt32LE b len
  b := pushUInt32LE b 0 -- rw_flags
  b := pushUInt64LE b userData
  while b.size < 64 do
    b := b.push 0
  return b

/-- Submit a single SQE (`NOP`, `READ`, or `WRITE`) and wait for 1 CQE completion, gated by `leansys_verify_io_uring_ring`. -/
def submitAndWaitOne (ring : IoUring) (opcode : UInt8) (targetFd : Int32)
    (fileOff bufAddr : UInt64) (bufLen : UInt32) (userData : UInt64) : IO (SysResult IoUringCqe) := do
  let some sqView := ring.sqRing.view? 0 ring.sqRing.lenBytes.toNat
    | return .error .einval
  let head := (sqView.getWord64LE ring.sqOffHead &&& 0xFFFFFFFF).toUInt32
  let tail := (sqView.getWord64LE ring.sqOffTail &&& 0xFFFFFFFF).toUInt32
  let mask := (sqView.getWord64LE ring.sqOffMask &&& 0xFFFFFFFF).toUInt32
  if verifyIoUringRing head tail ring.sqEntries mask 1 != 1 then
    return .error .eagain
  let slotIdx := (tail &&& mask).toNat
  let sqeBytes := buildSqe64 opcode targetFd fileOff bufAddr bufLen userData
  match ← mmapRegionWrite ring.sqesRegion (slotIdx * 64) sqeBytes with
  | .error e => return .error e
  | .ok _ =>
    match ← mmapRegionWrite ring.sqRing (ring.sqOffArray + slotIdx * 4) (pushUInt32LE ByteArray.empty slotIdx.toUInt32) with
    | .error e => return .error e
    | .ok _ =>
      match ← mmapRegionWrite ring.sqRing ring.sqOffTail (pushUInt32LE ByteArray.empty (tail + 1)) with
      | .error e => return .error e
      | .ok _ =>
        match ← ioUringEnterRaw ring.ringFd 1 1 1 with
        | .error e => return .error e
        | .ok _ =>
          let some cqView := ring.cqRing.view? 0 ring.cqRing.lenBytes.toNat
            | return .error .einval
          let cqHead := (cqView.getWord64LE ring.cqOffHead &&& 0xFFFFFFFF).toUInt32
          let cqTail := (cqView.getWord64LE ring.cqOffTail &&& 0xFFFFFFFF).toUInt32
          let cqMask := (cqView.getWord64LE ring.cqOffMask &&& 0xFFFFFFFF).toUInt32
          if cqHead == cqTail then
            return .error .eagain
          let cqeOff := ring.cqOffCqes + (cqHead &&& cqMask).toNat * 16
          let cqeBytes ← mmapRegionRead ring.cqRing cqeOff 16
          if cqeBytes.size < 16 then
            return .error .eio
          let ud := readUInt64LE cqeBytes 0
          let resU32 := readUInt32LE cqeBytes 8
          let flg := readUInt32LE cqeBytes 12
          discard <| mmapRegionWrite ring.cqRing ring.cqOffHead (pushUInt32LE ByteArray.empty (cqHead + 1))
          return .ok { userData := ud, res := resU32.toInt32, flags := flg }

/-- Submit an `IORING_OP_NOP` probe and verify round-trip `userData` completion. -/
def submitNop (ring : IoUring) (userData : UInt64 := 0xCAFEBABE) : IO (SysResult IoUringCqe) :=
  submitAndWaitOne ring opNop (-1) 0 0 0 userData

/-- Submit an `IORING_OP_READ` into a mapped `MmapRegion` slice `[regionOff, regionOff + len)` at `fileOff`. -/
def submitReadToRegion (ring : IoUring) (fd : Fd) (fileOff : UInt64)
    (dst : MmapRegion) (regionOff len : Nat) (userData : UInt64 := 1) : IO (SysResult IoUringCqe) := do
  if dst.readOnly || verifyBorrowedView dst.baseAddr.toUInt64 dst.lenBytes.toUInt64 regionOff.toUInt64 len.toUInt64 != 1 then
    return .error .einval
  let targetAddr := dst.baseAddr.toUInt64 + regionOff.toUInt64
  submitAndWaitOne ring opRead fd.raw.toInt32 fileOff targetAddr len.toUInt32 userData

/-- Submit an `IORING_OP_WRITE` from a mapped `MmapRegion` slice `[regionOff, regionOff + len)` to `fd` at `fileOff`. -/
def submitWriteFromRegion (ring : IoUring) (fd : Fd) (fileOff : UInt64)
    (src : MmapRegion) (regionOff len : Nat) (userData : UInt64 := 2) : IO (SysResult IoUringCqe) := do
  if verifyBorrowedView src.baseAddr.toUInt64 src.lenBytes.toUInt64 regionOff.toUInt64 len.toUInt64 != 1 then
    return .error .einval
  let srcAddr := src.baseAddr.toUInt64 + regionOff.toUInt64
  submitAndWaitOne ring opWrite fd.raw.toInt32 fileOff srcAddr len.toUInt32 userData

end IoUring

end LeanSys.Mmap
