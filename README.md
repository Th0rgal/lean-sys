# `lean-sys` — Verified Systems, Storage & Wire Runtime for Lean 4

`Th0rgal/lean-sys` is a standalone, `libleanrt.a`-only systems runtime for **Lean 4** (`leanprover/lean4:v4.31.0`) with **zero `import Lean`**, **zero `sorryAx`**, **10 audited non-vacuous formal specifications** (`LeanSys/Spec.lean`), and a **68-line leaf POSIX C shim** (`c/lean_sys_shim.c`).

It provides the crash-atomic storage (`LeanSys.Store`), zero-copy POSIX resource management (`LeanSys.Posix`), and bounded HTTP/1.1 transport (`LeanSys.Http`) for [`Th0rgal/maxwell`](https://github.com/Th0rgal/maxwell) and [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean) without linking `libsqlite3`, `libcurl`, or `libssl`.

## Architecture

1. **`LeanSys/Spec.lean` (Layer I Meta-Specs, Layer II Corollaries & Direct C-ABI Gates)**:
   - Exports unboxed C-ABI gates: `leansys_verify_slice_bounds`, `leansys_verify_wal_frame`, `leansys_verify_cas_digest`, `leansys_check_http_bounds`.
   - Audited in `< 4 ms` by `turbo-lean --json audit-spec LeanSys/Spec.lean` (`10/10 non_vacuous_and_tight`, `0 sorryAx`).
2. **`LeanSys/Posix.lean` + `c/lean_sys_shim.c` (Zero-Copy Borrowed FFI & Bracketed Lifecycle)**:
   - Borrowed `@& ByteArray` / `@& String` views (`ByteSlice`), packed 64-bit `(rc, errno)` return words decoded into `SysResult α := Except Errno α`, advisory `flock` (`withDirLock`), atomic `rename`/`link`, and process-group supervision (`withChildGroup` `-pgid` reaper).
3. **`LeanSys/Store.lean` (Crash-Atomic Append-Only WAL & Hardlinked CAS)**:
   - 16-byte WAL frames (`magic = 0x4C535953 "LSYS"`, `payloadLen`, 64-bit FNV-1a checksum) with automatic torn-tail truncation recovery on `openStore`, atomic compaction (`compact`), and zero-copy hardlinked CAS (`casPut`, `casMaterialize`).
4. **`LeanSys/Http.lean` (Zero-Copy Bounded HTTP/1.1 Server & Client)**:
   - Parses HTTP/1.1 headers and body slices over borrowed `ByteSlice` views gated by `leansys_check_http_bounds`.

## Quick Start

```bash
lake build
./.lake/build/bin/lean-sys-core self-test
turbo-lean --json audit-spec LeanSys/Spec.lean
```
