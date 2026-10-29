/-
  LeanSys.Posix: Zero-Copy POSIX FFI, Typed `Errno`/`SysResult`, and Resource Combinators
  (`0 import Lean`, `0 sorryAx`)
  - Borrowed FFI declarations (`@& String`, `@& ByteArray`, `@& Array String`)
  - Unboxed 64-bit `(rc, errno)` decoding into `SysResult α`
  - Resource-safe `Fd`, `DirLock`, and `ChildGroup` lifecycle combinators
-/
import LeanSys.Spec

namespace LeanSys.Posix

/-- Typed POSIX `errno` classification decoded from the upper 32 bits of an error return word. -/
inductive Errno where
  | eperm       -- 1
  | enoent      -- 2
  | esrch       -- 3
  | eintr       -- 4
  | eio         -- 5
  | ebadf       -- 9
  | echild      -- 10
  | eagain      -- 11 (EAGAIN / EWOULDBLOCK)
  | eacces      -- 13
  | eexist      -- 17
  | exdev       -- 18
  | einval      -- 22
  | enospc      -- 28
  | epiped      -- 32 (EPIPE)
  | enosys      -- 38 / 78 (ENOSYS)
  | eopnotsupp  -- 95 / 45 (EOPNOTSUPP / ENOTSUP)
  | econnrefused -- 111 / 61
  | unknown (raw : UInt32)
  deriving Repr, DecidableEq

namespace Errno

/-- Decode a raw POSIX `errno` integer into a typed `Errno`. -/
@[inline]
def ofUInt32 (code : UInt32) : Errno :=
  match code.toNat with
  | 1   => .eperm
  | 2   => .enoent
  | 3   => .esrch
  | 4   => .eintr
  | 5   => .eio
  | 9   => .ebadf
  | 10  => .echild
  | 11  => .eagain
  | 13  => .eacces
  | 17  => .eexist
  | 18  => .exdev
  | 22  => .einval
  | 28  => .enospc
  | 32  => .epiped
  | 38  => .enosys
  | 45  => .eopnotsupp
  | 61  => .econnrefused
  | 78  => .enosys
  | 95  => .eopnotsupp
  | 111 => .econnrefused
  | _   => .unknown code

/-- Render a concise diagnostic label for `Errno`. -/
def toString : Errno → String
  | .eperm        => "EPERM"
  | .enoent       => "ENOENT"
  | .esrch        => "ESRCH"
  | .eintr        => "EINTR"
  | .eio          => "EIO"
  | .ebadf        => "EBADF"
  | .echild       => "ECHILD"
  | .eagain       => "EAGAIN"
  | .eacces       => "EACCES"
  | .eexist       => "EEXIST"
  | .exdev        => "EXDEV"
  | .einval       => "EINVAL"
  | .enospc       => "ENOSPC"
  | .epiped       => "EPIPE"
  | .enosys       => "ENOSYS"
  | .eopnotsupp   => "EOPNOTSUPP"
  | .econnrefused => "ECONNREFUSED"
  | .unknown c    => s!"ERRNO_{c}"

instance : ToString Errno := ⟨Errno.toString⟩

end Errno

/-- Typed system call result parameterized by `Errno`. -/
abbrev SysResult (α : Type) := Except Errno α

/-- Decode a packed 64-bit C-shim return word (`bit 63 = error`, `bits 62..32 = errno`, `bits 62..0 = value`). -/
@[inline]
def decodePackedWord (w : UInt64) : SysResult UInt64 :=
  if (w &&& (1 : UInt64) <<< 63) != 0 then
    let errRaw : UInt32 := ((w >>> 32) &&& (0x7FFFFFFF : UInt64)).toUInt32
    .error (Errno.ofUInt32 errRaw)
  else
    .ok (w &&& (0x7FFFFFFFFFFFFFFF : UInt64))

/-! ## Raw Borrowed C-Shim Externs (`c/lean_sys_shim.c`) -/

@[extern "leansys_open_flock"]
opaque rawOpenFlock (path : @& String) (writable : UInt8) (exclusive : UInt8) (aux : UInt32) : IO UInt64

@[extern "leansys_fs_clone_or_link"]
opaque rawFsCloneOrLink (src : @& String) (dst : @& String) (op : UInt8) : IO UInt64

@[extern "leansys_write_all"]
opaque rawWriteAll (fd : UInt32) (ba : @& ByteArray) (off : USize) (len : USize) (mode : UInt8) : IO UInt64

@[extern "leansys_pread_ba"]
opaque rawPreadBa (fd : UInt32) (off : UInt64) (maxLen : USize) : IO ByteArray

@[extern "leansys_spawn_group"]
opaque rawSpawnGroup (cmd : @& String) (args : @& Array String) (roPath : @& String) (rwPath : @& String) (confine : UInt8) : IO UInt64

@[extern "leansys_kill_wait_group"]
opaque rawKillWaitGroup (pid : UInt32) (sig : UInt32) (nohang : UInt8) : IO UInt64

@[extern "leansys_net_listen"]
opaque rawNetListen (host : @& String) (port : UInt16) (backlog : UInt32) : IO UInt64

@[extern "leansys_net_accept_poll"]
opaque rawNetAcceptPoll (listenFd : UInt32) (timeoutMs : UInt32) (pollOnly : UInt8) : IO UInt64

/-! ## Zero-Copy ByteSlice over Borrowed `ByteArray` -/

/-- Validated zero-copy view `[off, off + len)` inside `ba : ByteArray`. -/
structure ByteSlice where
  ba  : ByteArray
  off : Nat
  len : Nat
  deriving Inhabited

namespace ByteSlice

/-- Construct a full-buffer `ByteSlice`. -/
@[inline]
def ofByteArray (ba : ByteArray) : ByteSlice :=
  { ba := ba, off := 0, len := ba.size }

/-- Construct a `ByteSlice` from a UTF-8 `String` without copying after UTF-8 view access. -/
@[inline]
def ofString (s : String) : ByteSlice :=
  ofByteArray s.toUTF8

/-- Verified sub-slice constructor gated by `LeanSys.Spec.verifySliceBounds`. -/
@[inline]
def subSlice? (s : ByteSlice) (relOff subLen : Nat) : Option ByteSlice :=
  let absOff := s.off + relOff
  if Spec.verifySliceBounds absOff.toUInt64 subLen.toUInt64 s.ba.size.toUInt64 == 1 then
    some { ba := s.ba, off := absOff, len := subLen }
  else
    none

/-- Total unchecked-free byte read relative to `s.off`. -/
@[inline]
def getByteD (s : ByteSlice) (idx : Nat) (fallback : UInt8 := 0) : UInt8 :=
  if idx < s.len && s.off + idx < s.ba.size then
    s.ba.get! (s.off + idx)
  else
    fallback

/-- Materialize a `ByteSlice` to a stand-alone `ByteArray` only when required by an API boundary. -/
def toByteArray (s : ByteSlice) : ByteArray :=
  if s.off == 0 && s.len == s.ba.size then
    s.ba
  else
    s.ba.extract s.off (s.off + s.len)

/-- Convert a `ByteSlice` to a UTF-8 `String` (lossless for valid UTF-8). -/
def toStringLossy (s : ByteSlice) : String :=
  String.fromUTF8! s.toByteArray

/-- Deterministic 64-bit FNV-1a hash over a `ByteSlice` without copying. -/
def fnv1a64 (s : ByteSlice) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  let limit := Nat.min (s.off + s.len) s.ba.size
  let mut i := s.off
  while i < limit do
    let b := s.ba.get! i
    h := (h ^^^ b.toUInt64) * 0x100000001b3
    i := i + 1
  return h

end ByteSlice

/-! ## Typed Resource Descriptors & Bracketed Lifecycle Combinators -/

/-- Linear file descriptor wrapper (`fd : UInt32`). -/
structure Fd where
  raw : UInt32
  deriving Repr, DecidableEq

/-- Exclusive advisory file lock handle (`flock(LOCK_EX)`). -/
structure DirLock where
  fd : Fd
  path : String
  deriving Repr

/-- Process-group child handle (`setpgid(pid, pid)`). -/
structure ChildGroup where
  pid : UInt32
  deriving Repr, DecidableEq

/-- Decode a non-error 64-bit descriptor word into `Fd`, enforcing lossless 32-bit preservation via `leansys_verify_fd_bounds`. -/
@[inline]
def decodeFdWord (v : UInt64) : SysResult Fd :=
  let fd32 := v.toUInt32
  if Spec.verifyFdBounds v fd32 == 1 then
    .ok ⟨fd32⟩
  else
    .error .einval

/-- Close a full 32-bit file descriptor (`wr = 3`, `aux = fd.raw` in `leansys_open_flock`, zero 16-bit truncation). -/
def closeFd (fd : Fd) : IO (SysResult Unit) := do
  let w ← rawOpenFlock "" 3 0 fd.raw
  match decodePackedWord w with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

/-- Open a file with `O_CLOEXEC` (`mode`: 0 = read-only, 1 = create+rw, 2 = create+append, 4 = create+trunc, 5 = existing rw without `O_CREAT`). -/
def openFd (path : String) (mode : UInt8 := 1) (exclusive : UInt8 := 0) (aux : UInt32 := 0) : IO (SysResult Fd) := do
  let w ← rawOpenFlock path mode exclusive aux
  match decodePackedWord w with
  | .ok v => pure (decodeFdWord v)
  | .error e => pure (.error e)

/-- Query the byte size of an open file descriptor via `fstat(2)` (`wr = 7` in `leansys_open_flock`). -/
def fstatSize (fd : Fd) : IO (SysResult UInt64) := do
  let w ← rawOpenFlock "" 7 0 fd.raw
  pure (decodePackedWord w)

/-- Duplicate `fd` to a descriptor `>= minBlocks64k * 65536` with `FD_CLOEXEC` (`F_DUPFD_CLOEXEC`, `wr = 8`). -/
def dupFdAbove64k (fd : Fd) (minBlocks64k : UInt8 := 1) : IO (SysResult Fd) := do
  let w ← rawOpenFlock "" 8 minBlocks64k fd.raw
  match decodePackedWord w with
  | .ok v => pure (decodeFdWord v)
  | .error e => pure (.error e)

/-- Probe the host Linux Landlock ABI version (`>= 1`), returning `.error .eopnotsupp` when Landlock is unavailable. -/
def probeLandlockAbi : IO (SysResult UInt32) := do
  let w ← rawOpenFlock "" 9 0 0
  match decodePackedWord w with
  | .ok v => pure (.ok v.toUInt32)
  | .error e => pure (.error e)

/-- Bracketed file-descriptor scope: guarantees `closeFd` runs even if `k` throws an IO exception. -/
def withFd (path : String) (mode : UInt8) (k : Fd → IO (SysResult α)) : IO (SysResult α) := do
  match ← openFd path mode with
  | .error e => pure (.error e)
  | .ok fd =>
    try
      k fd
    finally
      discard <| closeFd fd

/-- Acquire an exclusive `flock` on `lockPath` and run `k` inside a guaranteed release bracket. -/
def withDirLock (lockPath : String) (nonblock : Bool := false) (k : DirLock → IO (SysResult α)) : IO (SysResult α) := do
  let nb : UInt32 := if nonblock then 1 else 0
  let w ← rawOpenFlock lockPath 1 1 nb
  match decodePackedWord w with
  | .error e => pure (.error e)
  | .ok v =>
    match decodeFdWord v with
    | .error e => pure (.error e)
    | .ok fd =>
      try
        k ⟨fd, lockPath⟩
      finally
        discard <| closeFd fd

/-- Resize an open file descriptor to `sizeBytes` via `ftruncate(2)` (`mode = 3` in `leansys_write_all`). -/
def ftruncateFd (fd : Fd) (sizeBytes : Nat) : IO (SysResult Unit) := do
  let w ← rawWriteAll fd.raw ByteArray.empty sizeBytes.toUSize 0 3
  match decodePackedWord w with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

/-- Write `ba` at byte offset `offset` into a `MAP_SHARED` `mmap(2)` mapping of `fd` (`mode = 2` in `leansys_write_all`). -/
def mmapWriteShared (fd : Fd) (offset : Nat) (ba : ByteArray) : IO (SysResult Nat) := do
  let w ← rawWriteAll fd.raw ba offset.toUSize ba.size.toUSize 2
  match decodePackedWord w with
  | .ok n => pure (.ok n.toNat)
  | .error e => pure (.error e)

/-- Read `len` bytes starting at `offset` from a `MAP_SHARED` `mmap(2)` mapping of `fd` (`off | (2 << 62)` in `leansys_pread_ba`). -/
def mmapReadShared (fd : Fd) (offset : Nat) (len : Nat) : IO ByteArray :=
  let taggedOff : UInt64 := ((2 : UInt64) <<< 62) ||| (offset.toUInt64 &&& 0x3FFFFFFFFFFFFFFF)
  rawPreadBa fd.raw taggedOff len.toUSize

/-- Write an entire `ByteSlice` to `fd` (retrying on `EINTR` and optionally calling `fsync`). -/
def writeSliceAll (fd : Fd) (slice : ByteSlice) (doSync : Bool := false) : IO (SysResult Nat) := do
  if Spec.verifySliceBounds slice.off.toUInt64 slice.len.toUInt64 slice.ba.size.toUInt64 != 1 then
    return .error .einval
  let syncFlag : UInt8 := if doSync then 1 else 0
  let w ← rawWriteAll fd.raw slice.ba slice.off.toUSize slice.len.toUSize syncFlag
  match decodePackedWord w with
  | .ok n => pure (.ok n.toNat)
  | .error e => pure (.error e)

/-- Write an entire `ByteArray` to `fd`. -/
@[inline]
def writeAll (fd : Fd) (ba : ByteArray) (doSync : Bool := false) : IO (SysResult Nat) :=
  writeSliceAll fd (ByteSlice.ofByteArray ba) doSync

/-- Positional `pread` into a freshly allocated `ByteArray` of up to `maxLen` bytes. -/
@[inline]
def preadByteArray (fd : Fd) (offset : UInt64) (maxLen : Nat) : IO ByteArray :=
  rawPreadBa fd.raw offset maxLen.toUSize

/-- Sequential `read` (for sockets or pipes, passing `offset = UInt64.MAX`). -/
@[inline]
def readStreamChunk (fd : Fd) (maxLen : Nat) : IO ByteArray :=
  rawPreadBa fd.raw 0xFFFFFFFFFFFFFFFF maxLen.toUSize

/-- Atomically rename `src` to `dst` (`rename(2)`). -/
def atomicRename (src dst : String) : IO (SysResult Unit) := do
  let w ← rawFsCloneOrLink src dst 1
  match decodePackedWord w with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

/-- Mark `path` read-only (`chmod(path, 0444)`, `op = 2` in `leansys_fs_clone_or_link`). -/
def chmodReadOnly (path : String) : IO (SysResult Unit) := do
  let w ← rawFsCloneOrLink path "" 2
  match decodePackedWord w with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

/-- Query the byte size of `path` via `stat(2)` (`op = 3` in `leansys_fs_clone_or_link`). -/
def statFileSize (path : String) : IO (SysResult UInt64) := do
  let w ← rawFsCloneOrLink path "" 3
  pure (decodePackedWord w)

/-- Apply Linux Landlock ruleset restricting the calling thread/process to read/exec `roPath` (plus `/usr`,`/lib`,`/bin`) and read/write `rwPath` (`op = 4`).
    Fails closed with `.error .eopnotsupp` when Landlock is unavailable on the host OS/kernel. -/
def applyLandlockSelf (roPath rwPath : String) : IO (SysResult Unit) := do
  let w ← rawFsCloneOrLink roPath rwPath 4
  match decodePackedWord w with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

/-- Hardlink `src` to `dst` (unlinking any existing `dst` first). -/
def hardLinkReplace (src dst : String) : IO (SysResult Unit) := do
  let w ← rawFsCloneOrLink src dst 0
  match decodePackedWord w with
  | .ok _ => pure (.ok ())
  | .error e => pure (.error e)

/-- Spawn an isolated process group (`setpgid(0, 0)`) executing `cmd` with `args`,
    optionally applying Linux Landlock path confinement (`roPath`, `rwPath`) in the child before `execve`. -/
def spawnProcessGroupWithLandlock (cmd : String) (args : Array String)
    (roPath : String := "") (rwPath : String := "") (confine : Bool := false) : IO (SysResult ChildGroup) := do
  let w ← rawSpawnGroup cmd args roPath rwPath (if confine then 1 else 0)
  match decodePackedWord w with
  | .ok pid => pure (.ok ⟨pid.toUInt32⟩)
  | .error e => pure (.error e)

/-- Spawn an isolated process group (`setpgid(0, 0)`) executing `cmd` with `args`. -/
def spawnProcessGroup (cmd : String) (args : Array String) : IO (SysResult ChildGroup) :=
  spawnProcessGroupWithLandlock cmd args "" "" false

/-- Synchronously poll or wait on a `ChildGroup` (`sig = 0` for status poll, `sig = 9`/`15` to kill `-pgid`).
    Returns `some exitCode` if the process exited, or `none` if still running (`WNOHANG`). -/
def waitOrKillGroup (cg : ChildGroup) (sig : UInt32 := 0) (nohang : Bool := false) : IO (SysResult (Option UInt32)) := do
  let nh : UInt8 := if nohang then 1 else 0
  let w ← rawKillWaitGroup cg.pid sig nh
  match decodePackedWord w with
  | .error e => pure (.error e)
  | .ok packed =>
    if packed == 0 then
      pure (.ok none)
    else
      pure (.ok (some (packed &&& 0xFFFF).toUInt32))

/-- Run a child process group with optional pre-`execve` Landlock confinement in a bracketed scope
    that guarantees `SIGKILL` (`-pgid`) and `waitpid` reaper on exit. -/
def withChildGroupWithLandlock (cmd : String) (args : Array String)
    (roPath : String) (rwPath : String) (confine : Bool)
    (k : ChildGroup → IO (SysResult α)) : IO (SysResult α) := do
  match ← spawnProcessGroupWithLandlock cmd args roPath rwPath confine with
  | .error e => pure (.error e)
  | .ok cg =>
    try
      k cg
    finally
      discard <| waitOrKillGroup cg 9 false

/-- Run a child process group in a bracketed scope that guarantees `SIGKILL` (`-pgid`) and `waitpid` reaper on exit. -/
def withChildGroup (cmd : String) (args : Array String) (k : ChildGroup → IO (SysResult α)) : IO (SysResult α) :=
  withChildGroupWithLandlock cmd args "" "" false k

/-- Bind and listen on `host:port` (`port = 0` selects an ephemeral port). Returns `(listenFd, boundPort)`. -/
def tcpListen (host : String) (port : UInt16) (backlog : UInt32 := 64) : IO (SysResult (Fd × UInt16)) := do
  let w ← rawNetListen host port (if backlog == 0 then 16 else backlog)
  match decodePackedWord w with
  | .error e => pure (.error e)
  | .ok packed =>
    let rawFd64 := packed &&& 0xFFFFFFFF
    match decodeFdWord rawFd64 with
    | .error e => pure (.error e)
    | .ok fd =>
      let boundPort : UInt16 := ((packed >>> 32) &&& 0xFFFF).toUInt16
      pure (.ok (fd, boundPort))

/-- Connect a TCP client socket to `host:port` (`backlog = 0` mode in `leansys_net_listen`). -/
def tcpConnect (host : String) (port : UInt16) : IO (SysResult Fd) := do
  let w ← rawNetListen host port 0
  match decodePackedWord w with
  | .error e => pure (.error e)
  | .ok fdWord => pure (decodeFdWord fdWord)

/-- Poll `listenFd` for up to `timeoutMs` and accept one `SOCK_CLOEXEC` client connection. -/
def tcpAcceptPoll (listenFd : Fd) (timeoutMs : UInt32 := 1000) : IO (SysResult Fd) := do
  let w ← rawNetAcceptPoll listenFd.raw timeoutMs 0
  match decodePackedWord w with
  | .error e => pure (.error e)
  | .ok clientWord => pure (decodeFdWord clientWord)

/-- Poll an existing connected socket/pipe `fd` for `POLLIN` readability up to `timeoutMs` (`pollOnly = 1`),
    returning `.ok ()` when readable or `.error .eagain` on timeout. -/
def pollReadable (fd : Fd) (timeoutMs : UInt32 := 2000) : IO (SysResult Unit) := do
  let w ← rawNetAcceptPoll fd.raw timeoutMs 1
  match decodePackedWord w with
  | .error e => pure (.error e)
  | .ok _ => pure (.ok ())

end LeanSys.Posix
