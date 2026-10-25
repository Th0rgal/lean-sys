# `lean-sys` — Verified Systems, Storage & Wire Runtime for Lean 4

`Th0rgal/lean-sys` is a standalone, `libleanrt.a`-only systems runtime for **Lean 4** (`leanprover/lean4:v4.35.0`) with **zero `import Lean`**, **zero `sorryAx`**, **<!-- inventory:leansys_total_tight -->36<!-- /inventory:leansys_total_tight --> audited non-vacuous formal specifications** (`LeanSys/Spec.lean` + `LeanSys/Hash.lean` + `LeanSys/Gate.lean` + `LeanSys/Contracts/MetaGate.lean` + `LeanSys/Contracts/SpeculativeGate.lean`), **<!-- inventory:leansys_cabi -->26<!-- /inventory:leansys_cabi --> unboxed C-ABI safety gates**, and a **<!-- inventory:leansys_shim_loc -->51<!-- /inventory:leansys_shim_loc -->-line leaf POSIX C shim** (`c/lean_sys_shim.c`).

It provides the crash-atomic storage (`LeanSys.Store`, `LeanSys.Lsm`), shared-memory IPC (`LeanSys.Mmap`), zero-copy JSON/JSONL tape indexing (`LeanSys.Codec`), 64-bit word-strided hashing (`LeanSys.Hash`), process-group quota sandboxing (`LeanSys.Sandbox`), and bounded HTTP/1.1 Keep-Alive transport (`LeanSys.Http`, `LeanSys.Reactor`) for [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean) and [`Th0rgal/lean-native`](https://github.com/Th0rgal/lean-native) without linking `libsqlite3`, `libcurl`, or `libssl`.

## Architecture

1. **`LeanSys/Spec.lean` + `LeanSys/Gate.lean` + `LeanSys/Contracts/{MetaGate,SpeculativeGate}.lean` (Layer I Meta-Specs, Layer II Corollaries & <!-- inventory:leansys_cabi -->26<!-- /inventory:leansys_cabi --> Direct C-ABI Gates)**:
   - Exports <!-- inventory:leansys_cabi -->26<!-- /inventory:leansys_cabi --> unboxed C-ABI gates: `leansys_verify_slice_bounds`, `leansys_verify_wal_frame`, `leansys_verify_cas_digest`, `leansys_check_http_bounds`, `leansys_verify_jsonl_tape`, `leansys_verify_ring_cursor`, `leansys_verify_sst_block`, `leansys_verify_poll_interest`, `leansys_verify_rlimit_budget`, `leansys_verify_composite_key_order`, `leansys_verify_token_auth`, `leansys_verify_log_window`, `leansys_verify_jsonrpc_frame`, `leansys_gate_admit`, `leansys_verify_mmap_seqlock`, `leansys_verify_proc_stat_fields`, and `leansys_mix64_word`.
   - Audited in `< 2 ms` by `turbo-lean --json audit-spec LeanSys/Spec.lean` (`<!-- inventory:leansys_total_tight -->36<!-- /inventory:leansys_total_tight -->/<!-- inventory:leansys_total_tight -->36<!-- /inventory:leansys_total_tight --> non_vacuous_and_tight`, `0 sorryAx`).
2. **`LeanSys/Hash.lean` & `LeanSys/Codec.lean` (Word-Strided Hashing, 64-Bit Bloom Filter & Zero-Copy `JsonTape`)**:
   - Unrolled 32-byte/8-byte word-strided `xxh64Slice` (`~750 MB/s`), machine-checked zero-false-negative 3-probe Bloom filter (`bloom_no_false_negative`), and zero-copy `JsonTape` field indexer (`>110M lookup ops/s`).
3. **`LeanSys/Posix.lean` + `c/lean_sys_shim.c` (`51 LOC` Leaf C Shim & Bracketed Lifecycle)**:
   - Borrowed `@& ByteArray` / `@& String` views (`ByteSlice`), packed 64-bit `(rc, errno)` return words decoded into `SysResult α := Except Errno α`, advisory `flock` (`withDirLock`), atomic `rename`/`link`, and process-group supervision (`withChildGroup` `-pgid` reaper).
4. **`LeanSys/Store.lean`, `LeanSys/Lsm.lean` & `LeanSys/Mmap.lean` (Crash-Atomic WAL, Hardlinked CAS, SST & `/dev/shm` Ring)**:
   - Single-buffer WAL frame encoding and `putBatch` group-commit (`~1.25M frames/s`), automatic torn-tail truncation recovery on `openStore`, sorted-string tables (`SstTable`, `~2.2M lookups/s`), and `/dev/shm` SPSC ring buffers (`ShmRing`).
5. **`LeanSys/Http.lean`, `LeanSys/Reactor.lean` & `LeanSys/Sandbox.lean` (HTTP/1.1 Keep-Alive Poll Reactor & Quota Enforcer)**:
   - Zero-copy HTTP/1.1 parser, multi-request Keep-Alive connection loop gated by `leansys_verify_poll_interest`, and subprocess quota sandbox gated by `leansys_verify_rlimit_budget`.

## Quick Start

```bash
./scripts/ci_verify.sh
python3 autoresearch/sys_arena.py --json
```
