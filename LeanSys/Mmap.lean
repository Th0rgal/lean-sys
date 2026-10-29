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
    if fsz < (24 + cap).toUInt64 then
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
    if fsz < (24 + cap).toUInt64 then
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
    if fsz < 24 then
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
        if magic != ringMagic || cap < 64 || fsz < (24 + cap.toUInt64) then
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

end LeanSys.Mmap
