# AGENTS.md — Architectural Charter (`lean-sys` ⟷ `turbo-lean` ⟷ `maxwell` ⟷ `orb`)

## 1. Symbiosis & Architectural Roles

`lean-sys` is the **Verified Systems, Storage, and Network Runtime Foundation** (`0 import Lean`, `0 sorryAx`, `libleanrt.a`-only) for the 5-repository Certified Research & Orchestration stack:

- **`lean-sys` (`Th0rgal/lean-sys` v0.2 — Verified POSIX, Crash-Atomic WAL/CAS, Composite-Key Table, Token Auth, Sliding-Window Log & JSON-RPC 2.0 Runtime)**:
  Provides <!-- inventory:leansys_cabi -->17<!-- /inventory:leansys_cabi --> unboxed C-ABI safety gates (`LeanSys/Spec.lean` + `LeanSys/Gate.lean`), a tiny leaf-only C shim (`c/lean_sys_shim.c`, `<!-- inventory:leansys_shim_loc -->51<!-- /inventory:leansys_shim_loc --> LOC ≤ 65 LOC`), zero-copy borrowed `ByteSlice` views, bracketed POSIX descriptors (`Fd`, `DirLock`, `ChildGroup` `-pgid` reaper), a crash-atomic append-only WAL + hardlinked CAS (`LeanSys/Store.lean`), composite-key range & secondary-index tables (`LeanSys/Table.lean`), token-rotation/revocation/expiry auth (`LeanSys/Auth.lean`), sliding-window stdout/stderr tail log rings (`LeanSys/ProcLog.lean`), zero-copy JSON-RPC 2.0 envelope codecs (`LeanSys/JsonRpc.lean`), and a zero-copy bounded HTTP/1.1 engine (`LeanSys/Http.lean`).
- **`orb` (`Th0rgal/sandboxed.sh` — Formal Orchestration & Node Lifecycle Kernel)**:
  Compiles `lean/Orb/Spec.lean` (`0 import Lean`, `0 sorryAx`, `16/16` tight specs, `12` C-ABI exports at `2.288 ns/call`) directly into `liborb_spec_cabi.a` via `build.rs` and `src/orb_spec.rs`, gating writer worktree reuse (`orb_verify_writer_reuse`), lease mode algebra (`orb_verify_lease_mode`), track hold duration (`orb_verify_track_hold`), repo disjointness (`orb_verify_repo_disjoint`), remote outbox transitions (`orb_verify_remote_outbox`), DAG task board slot admission & retry budgets (`orb_verify_board_slots`, `orb_verify_board_retry`), durable workspace job state transitions (`orb_verify_job_transition`), remote protocol bundle budgets (`orb_verify_bundle_budget`), token rotation (`orb_verify_token_rotation`), and sliding-window process logs (`leansys_verify_log_window`).
- **`turbo-lean` (`Th0rgal/turbo-lean` — Incremental Verification, Zygote Elaboration & Spec Auditor)**:
  Links all <!-- inventory:leansys_cabi -->17<!-- /inventory:leansys_cabi --> `lean-sys` C-ABI gates (`leansys_verify_*`, `leansys_check_http_bounds`, `leansys_gate_admit`, `leansys_mix64_word`) into both `TurboLean/ShmIpc.lean` and the Rust coordinator (`c_abi.rs`, `db.rs`), auditing `LeanSys/Spec.lean` and `Orb/Spec.lean` for non-vacuity and tightness (`0 vacuous`, `0 trivial`, `0 horizontal_packing_warnings`).
- **`maxwell` (`Th0rgal/maxwell` — The Maxwell Gate & Self-Refining Loop)**:
  Embeds `LeanSys.Store`, `LeanSys.Table`, `LeanSys.Auth`, `LeanSys.ProcLog`, `LeanSys.JsonRpc`, and `LeanSys.Http` inside `maxwell-core` (`serve-telemetry`, `spool-append`, `stream`) to ingest, index, authenticate, and spool campaign telemetry without SQLite or external C network libraries.
- **`lean-native` (`Th0rgal/lean-native` — Verified LCNF/LNIR Native & GPU Compiler)**:
  Remains strictly focused on pure numeric/tensor/ISA codegen and symbolic translation validation (`SymbolicTV`), free of POSIX socket or storage concerns.

```
Wire / Disk I/O ──► Stage 0: Unboxed C-ABI Bounds & Auth Gate (`LeanSys/Spec.lean` & `Orb/Spec.lean`, `~1.8-2.3 ns`)
                ──► Stage 1: Borrowed Zero-Copy Slice & POSIX Shim (`c/lean_sys_shim.c` + `Posix.lean`)
                ──► Stage 2: Crash-Atomic WAL / Table / CAS / Auth / JSON-RPC / HTTP (`Store` + `Table` + `Auth` + `JsonRpc` + `Http`)
                ──► Stage 3: Spec Audit & Symbol Hygiene Gate (`turbo-lean audit-spec` + `nm -u`)
```

---

## 2. Seven Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Direct Unboxed C-ABI (`@[inline, export]`)**:
   Every buffer boundary check, WAL frame integrity check, CAS path-traversal check, composite-key order check, token auth check, sliding-window log bound check, JSON-RPC 2.0 envelope check, and orchestration state transition must live in `LeanSys/Spec.lean` or `Orb/Spec.lean` (zero `import Lean`, zero `sorryAx`) and export an unboxed C-ABI symbol (`leansys_verify_*`, `orb_verify_*`) called directly by both Lean and Rust host runtimes (`turbo-lean` `c_abi.rs`, `orb` `src/orb_spec.rs`).

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries ≤ 3 Lines)**:
   - **Layer I (Universal Systems Meta-Specifications)**: Structural systems reasoning lives in reusable combinators (`MetaGateSpec`, `TotalSliceParserSpec`, `FramedCodecSpec`, `CrashAtomicLogSpec`, `ProtocolRefinementSpec`, `LinearLeaseSpec`, `IdempotentOutboxSpec`, `DagScheduleSpec`, `QuotaCircuitSpec`) plus shared Layer-0 contracts in `LeanSys/Contracts/MetaGate.lean` and `LeanSys/Contracts/SpeculativeGate.lean`.
   - **Layer II (Declarative Corollaries)**: Concrete subsystem invariants (slice bounds, WAL torn-tail truncation recovery, CAS digest/path safety, HTTP bounds, composite-key lexicographic order, token rotation/revocation/expiry, sliding-window log truncation, JSON-RPC 2.0 framing, linear FD lifecycle) are instantiated as `MetaGateSpec` / `CrashAtomicLogSpec` bundles and **≤ 3-line corollaries**.

3. **Zero-Allocation Borrowed FFI & Packed 64-Bit Syscall Return Words**:
   - All C externs in `LeanSys/Posix.lean` borrow Lean buffers via `@& String`, `@& ByteArray`, and `@& Array String` (`b_lean_obj_arg`) so the C shim never mutates reference counts or clones payloads.
   - Syscalls pack `(rc, errno)` into a single 64-bit word (`bit 63 = error`, `bits 62..32 = errno`, `bits 62..0 = value`), decoded in Lean into `SysResult α := Except Errno α`.

4. **Strict TCB & Dependency Hygiene (`c/lean_sys_shim.c ≤ 65 LOC`, `0 import Lean`)**:
   - `lean-sys-core` must link **only** against `libleanrt.a` and standard POSIX `libc` (`supportInterpreter := false`).
   - **Zero `import Lean`**, **zero `libsqlite3`**, **zero `libcurl`/`libssl`**, and **zero parsing or allocation logic in C**. The C shim (`51 LOC`) is restricted to leaf POSIX syscall wrappers (`open`/`flock`, `rename`/`link`, `send`/`write`/`fsync`, `pread`/`read`, `fork`/`setpgid`/`execve`/`waitpid`, `socket`/`bind`/`listen`/`accept4`/`poll`).

5. **Mathlib4 Algebraic Proof Style**:
   Proofs in `LeanSys/Spec.lean` must use concise algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, induction with single-line branches). Verbose `cases <;> cases` trees are forbidden.

6. **LOC & Trust-Surface Ratchet ($\Delta\text{LOC}_{\text{C}} \le 0$)**:
   Every feature addition or optimization must preserve or shrink the C shim footprint (`51 LOC ≤ 65 LOC`) and generalize Layer I combinators in `LeanSys/Spec.lean` rather than accreting ad-hoc parsers or unsafe FFI glue.

7. **Doc & Context Ratchet (`--sync-docs`)**:
   Any commit that changes theorems, tight specs, or C-ABI exports must keep `README.md` and `AGENTS.md` aligned with the verified inventory (<!-- inventory:leansys_summary -->25/25 tight specs (23 in Spec.lean + 2 in Hash.lean + 1 in Gate.lean, 17 C-ABI exports, c/lean_sys_shim.c=51 LOC, 0 sorryAx)<!-- /inventory:leansys_summary -->). `./scripts/ci_verify.sh --sync-docs` enforces that check.

---

## 3. Repository Layout & Verification Entrypoints

- **Formal Systems Specifications & <!-- inventory:leansys_cabi -->17<!-- /inventory:leansys_cabi --> C-ABI Gates**: [`LeanSys/Spec.lean`](LeanSys/Spec.lean), [`LeanSys/Gate.lean`](LeanSys/Gate.lean), [`LeanSys/Contracts/MetaGate.lean`](LeanSys/Contracts/MetaGate.lean), [`LeanSys/Contracts/SpeculativeGate.lean`](LeanSys/Contracts/SpeculativeGate.lean) (`<!-- inventory:leansys_total_tight -->25<!-- /inventory:leansys_total_tight -->/<!-- inventory:leansys_total_tight -->25<!-- /inventory:leansys_total_tight --> non_vacuous_and_tight`, `<!-- inventory:leansys_cabi -->17<!-- /inventory:leansys_cabi -->` C-ABI exports)
- **64-Bit Word-Strided Hash (`xxh64Slice`) & 3-Probe Bloom Filter**: [`LeanSys/Hash.lean`](LeanSys/Hash.lean) (`or_and_self`, `bloom_no_false_negative`)
- **Zero-Copy JSON/JSONL Tape Indexer (`JsonTape`)**: [`LeanSys/Codec.lean`](LeanSys/Codec.lean)
- **Leaf POSIX C Shim (`51 LOC`) & Typed FFI**: [`c/lean_sys_shim.c`](c/lean_sys_shim.c), [`LeanSys/Posix.lean`](LeanSys/Posix.lean)
- **Crash-Atomic WAL (`putBatch` Group-Commit) & Hardlinked CAS**: [`LeanSys/Store.lean`](LeanSys/Store.lean)
- **Composite-Key Range Scans & Secondary Index Table (`IndexedTable`)**: [`LeanSys/Table.lean`](LeanSys/Table.lean)
- **Token Rotation, Revocation Generation & Expiry Auth (`TokenVerifier`)**: [`LeanSys/Auth.lean`](LeanSys/Auth.lean)
- **Bounded Sliding-Window Process Tail Log (`SlidingLogRing`)**: [`LeanSys/ProcLog.lean`](LeanSys/ProcLog.lean)
- **Zero-Copy JSON-RPC 2.0 Envelope Validator & Codec (`JsonRpc`)**: [`LeanSys/JsonRpc.lean`](LeanSys/JsonRpc.lean)
- **Sorted-String Table (`SstTable`) & 64-Bit Bloom Engine**: [`LeanSys/Lsm.lean`](LeanSys/Lsm.lean)
- **Shared-Memory `/dev/shm` SPSC Ring Buffer (`ShmRing`)**: [`LeanSys/Mmap.lean`](LeanSys/Mmap.lean)
- **Zero-Copy Bounded HTTP/1.1 Engine & Keep-Alive Poll Reactor**: [`LeanSys/Http.lean`](LeanSys/Http.lean), [`LeanSys/Reactor.lean`](LeanSys/Reactor.lean)
- **Process-Group Quota Sandbox (`-pgid` Reaper & `rlimit` Gate)**: [`LeanSys/Sandbox.lean`](LeanSys/Sandbox.lean)
- **Standalone Native Self-Test & Benchmark Binary**: [`LeanSys/Core.lean`](LeanSys/Core.lean) (`./.lake/build/bin/lean-sys-core [self-test|bench]`)
- **Closed-Loop Autoresearch Arena & CI Gate**: [`autoresearch/sys_arena.py`](autoresearch/sys_arena.py), [`scripts/ci_verify.sh`](scripts/ci_verify.sh)

### Mandatory 3-Gate Pre-Commit Verification

```bash
# Gate 1: Build standalone libleanrt-only binary & run deterministic self-test
lake build && ./.lake/build/bin/lean-sys-core self-test

# Gate 2: Two-level specification non-vacuity & tightness audit (0 vacuous, 0 trivial, 0 sorryAx)
turbo-lean --json audit-spec LeanSys/Spec.lean

# Gate 3: Binary TCB symbol hygiene (must return empty — no frontend, no SQLite, no OpenSSL)
nm -u .lake/build/bin/lean-sys-core | grep -E 'lean_elab|lean_environment|sqlite|SSL_' || echo "TCB_CLEAN"
```

---

## 4. Optimization Objectives & Resource Envelopes (`ObjectiveReceipt`)

Autonomous research on `lean-sys` separates **Layer 1 (Formal Admissibility & TCB Hygiene)** from **Layer 2 (Lexicographic Empirical Fitness)**:

1. **Layer 1 — Hard Formal & TCB Gate (`LeanSys/Spec.lean`, `G(x) = true`)**:
   - `slice_bounds_rejects_overflow`, `wal_frame_rejects_corrupt_or_torn`, `wal_torn_tail_recovers_committed`, `cas_gate_rejects_tampered_or_traversal`, `http_gate_rejects_invalid_envelope`, `composite_key_order_rejects_inversion`, `token_auth_rejects_revoked_expired_or_forged`, `log_window_rejects_overflow`, `jsonrpc_frame_rejects_malformed`, `fd_lifecycle_rejects_unsafe`.
   - `0 sorryAx`, `0 vacuous` specs (`turbo-lean --json audit-spec LeanSys/Spec.lean`), and `0` forbidden symbols in `nm -u lean-sys-core`.
2. **Layer 2 — Lexicographic Objective (`J_sys`)**:
   - **Primary**: Maximize I/O & RPC throughput geomean $\text{Geomean}(\text{Throughput}_{\text{WAL}}, \text{Throughput}_{\text{CAS}}, \text{Req/s}_{\text{HTTP/IPC}})$ and minimize tail latency $\text{p99}_{\mu\text{s}}$.
   - **Secondary**: Minimize heap allocations per request (`alloc_bytes / op`) and stripped binary size (`< 2.5 MB`).
   - **Resource Envelope**: $\text{LOC}(\text{c/lean\_sys\_shim.c}) \le 65$ (`51 LOC`), $\text{FD}_{\text{leaked}} = 0$, $\text{OrphanProcesses} = 0$, and $\Delta\text{LOC} \le 0$.
