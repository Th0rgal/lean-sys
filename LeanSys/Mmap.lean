/-
  LeanSys.Mmap: Shared-Memory (`/dev/shm`) SPSC Ring Buffer & Zero-Copy Slot Arena
  (`0 import Lean`, `0 sorryAx`)
  - 24-byte ring header (`magic = 0x4C524E47 "LRNG"`, `cap : UInt32`, `head : UInt64`, `tail : UInt64`)
  - Every `push` and `pop` is gated by `LeanSys.Spec.verifyRingCursor` (`leansys_verify_ring_cursor`)
  - Length-prefixed frames (`msgLen : UInt32` + `payload`) inside a fixed-capacity `/dev/shm` arena
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

/-- Shared-memory SPSC ring handle backed by `/dev/shm` (or tmpfs). -/
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

/-- Initialize a fresh `ShmRing` at `path` with data capacity `cap` bytes (rounded up to >= 64). -/
def init (path : String) (cap : UInt32 := 65536) : IO (SysResult ShmRing) := do
  let effCap : UInt32 := if cap < 64 then 64 else cap
  let lockPath := path ++ ".lock"
  let hdr := encodeHeader effCap 0 0
  withDirLock lockPath false fun _ => do
    match ← withFd path 4 (fun fd => writeAll fd hdr false) with
    | .error e => pure (.error e)
    | .ok _ => pure (.ok { path := path, lockPath := lockPath, cap := effCap })

/-- Read `(magic, cap, head, tail)` and the current ring image from `r.path`. -/
def readImage (r : ShmRing) : IO (SysResult (UInt32 × UInt32 × UInt64 × UInt64 × ByteArray)) := do
  match ← withFd r.path 0 (fun fd => do
    let buf ← preadByteArray fd 0 (24 + r.cap.toNat)
    pure (.ok buf)) with
  | .error e => pure (.error e)
  | .ok buf =>
    if buf.size < 24 then
      pure (.error .eio)
    else
      let magic := readUInt32LE buf 0
      let cap := readUInt32LE buf 4
      let head := readUInt64LE buf 8
      let tail := readUInt64LE buf 16
      if magic != ringMagic || cap == 0 then
        pure (.error .einval)
      else
        pure (.ok (magic, cap, head, tail, buf))

/-- Push a `ByteSlice` message into `ShmRing`, gated by `leansys_verify_ring_cursor` under `withDirLock`. -/
def push (r : ShmRing) (msg : ByteSlice) : IO (SysResult Unit) := do
  let frameLen : UInt64 := (4 + msg.len).toUInt64
  withDirLock r.lockPath false fun _ => do
    match ← readImage r with
    | .error e => pure (.error e)
    | .ok (_, cap, head, tail, buf) =>
      if verifyRingCursor head tail cap.toUInt64 frameLen != 1 then
        pure (.error .enospc)
      else
        let unreadLen := (head - tail).toNat
        let unreadSlice :=
          if 24 + unreadLen ≤ buf.size then
            buf.extract 24 (24 + unreadLen)
          else
            ByteArray.empty
        let newHead := head + frameLen
        let mut out := encodeHeader cap newHead tail
        out := out ++ unreadSlice
        out := pushUInt32LE out msg.len.toUInt32
        out := out ++ msg.toByteArray
        match ← withFd r.path 4 (fun fd => writeAll fd out false) with
        | .error e => pure (.error e)
        | .ok _ => pure (.ok ())

/-- Pop the oldest message from `ShmRing` as a `ByteArray` (`none` if the ring is empty). -/
def pop? (r : ShmRing) : IO (SysResult (Option ByteArray)) := do
  withDirLock r.lockPath false fun _ => do
    match ← readImage r with
    | .error e => pure (.error e)
    | .ok (_, cap, head, tail, buf) =>
      if head == tail then pure (.ok none)
      else if verifyRingCursor head tail cap.toUInt64 0 != 1 then pure (.error .einval)
      else
        let unreadLen := (head - tail).toNat
        if unreadLen < 4 || 24 + unreadLen > buf.size then pure (.error .eio)
        else
          let msgLen := (readUInt32LE buf 24).toNat
          let frameLen := 4 + msgLen
          if frameLen > unreadLen then pure (.error .eio)
          else
            let newTail := tail + frameLen.toUInt64
            if verifyRingCursor head newTail cap.toUInt64 frameLen.toUInt64 != 1 then pure (.error .einval)
            else
              let payload := buf.extract 28 (28 + msgLen)
              let remSlice := buf.extract (24 + frameLen) (24 + unreadLen)
              let out := encodeHeader cap head newTail ++ remSlice
              match ← withFd r.path 4 (fun fd => writeAll fd out false) with
              | .error e => pure (.error e)
              | .ok _ => pure (.ok (some payload))

/-- Validate a shared-memory seqlock snapshot read across process restarts via `leansys_verify_mmap_seqlock`. -/
@[inline]
def validateSeqlockSnapshot (schemaVersion expectedVersion : UInt32)
    (seqBefore seqAfter writerEpoch minEpoch payloadLen ringCap : UInt64) : Bool :=
  verifyMmapSeqlock mmapSeqlockMagic schemaVersion expectedVersion
    seqBefore seqAfter writerEpoch minEpoch payloadLen ringCap == 1

end ShmRing

end LeanSys.Mmap
