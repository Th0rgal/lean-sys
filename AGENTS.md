# AGENTS.md — Architectural Charter (`lean-sys` ⟷ `turbo-lean` ⟷ `maxwell`)

## 1. Symbiosis & Architectural Roles

`lean-sys` is the **Verified Systems, Storage, and Network Runtime Foundation** (`0 import Lean`, `0 sorryAx`, `libleanrt.a`-only) for the 4-repository Certified Research stack:

- **`lean-sys` (`Th0rgal/lean-sys` — Verified POSIX, Crash-Atomic WAL/CAS & Zero-Copy Wire Runtime)**:
  Provides unboxed C-ABI safety gates (`LeanSys/Spec.lean`), a tiny leaf-only C shim (`c/lean_sys_shim.c`, `≤ 70 LOC`), zero-copy borrowed `ByteSlice` views, bracketed POSIX descriptors (`Fd`, `DirLock`, `ChildGroup` `-pgid` reaper), a crash-atomic append-only WAL + hardlinked CAS (`LeanSys/Store.lean`), and a zero-copy bounded HTTP/1.1 engine (`LeanSys/Http.lean`).
- **`turbo-lean` (`Th0rgal/turbo-lean` — Incremental Verification, Zygote Elaboration & Spec Auditor)**:
  Links `lean-sys` C-ABI gates (`leansys_verify_slice_bounds`, `leansys_verify_wal_frame`, `leansys_verify_cas_digest`, `leansys_check_http_bounds`) into both `TurboLean/ShmIpc.lean` and the Rust coordinator (`c_abi.rs`, `db.rs`), auditing `LeanSys/Spec.lean` for non-vacuity and tightness (`0 vacuous`, `0 trivial`).
- **`maxwell` (`Th0rgal/maxwell` — The Maxwell Gate & Self-Refining Loop)**:
  Embeds `LeanSys.Store` and `LeanSys.Http` inside `maxwell-core` (`serve-telemetry`, `spool-append`) to ingest, deduplicate, and spool campaign telemetry without SQLite or external C network libraries.
- **`lean-native` (`Th0rgal/lean-native` — Verified LCNF/LNIR Native & GPU Compiler)**:
  Remains strictly focused on pure numeric/tensor/ISA codegen and symbolic translation validation (`SymbolicTV`), free of POSIX socket or storage concerns.

```
Wire / Disk I/O ──► Stage 0: Unboxed C-ABI Bounds & Auth Gate (`LeanSys/Spec.lean`, `< 2 ns`)
                ──► Stage 1: Borrowed Zero-Copy Slice & POSIX Shim (`c/lean_sys_shim.c` + `Posix.lean`)
                ──► Stage 2: Crash-Atomic WAL / Hardlinked CAS / HTTP (`Store.lean` + `Http.lean`)
                ──► Stage 3: Spec Audit & Symbol Hygiene Gate (`turbo-lean audit-spec` + `nm -u`)
```

---

## 2. Six Non-Negotiable Engineering Rules

1. **Zero Model-Code Gap via Direct Unboxed C-ABI (`@[inline, export]`)**:
   Every buffer boundary check, WAL frame integrity check, CAS path-traversal check, and protocol envelope check must live in `LeanSys/Spec.lean` (zero `import Lean`, zero `sorryAx`) and export an unboxed C-ABI symbol (`leansys_verify_*`, `leansys_check_*`) called directly by both Lean (`LeanSys/*.lean`) and host runtimes (`turbo-lean` `c_abi.rs`).

2. **Two-Layer Specification Compression (`Layer I` Meta-Specs vs. `Layer II` Corollaries ≤ 3 Lines)**:
   - **Layer I (Universal Systems Meta-Specifications)**: Structural systems reasoning lives in reusable combinators (`MetaGateSpec`, `TotalSliceParserSpec`, `FramedCodecSpec`, `CrashAtomicLogSpec`, `ProtocolRefinementSpec`).
   - **Layer II (Declarative Corollaries)**: Concrete subsystem invariants (slice bounds, WAL torn-tail truncation recovery, CAS digest/path safety, HTTP bounds, linear FD lifecycle) are instantiated as `MetaGateSpec` / `CrashAtomicLogSpec` bundles and **≤ 3-line corollaries**.

3. **Zero-Allocation Borrowed FFI & Packed 64-Bit Syscall Return Words**:
   - All C externs in `LeanSys/Posix.lean` borrow Lean buffers via `@& String`, `@& ByteArray`, and `@& Array String` (`b_lean_obj_arg`) so the C shim never mutates reference counts or clones payloads.
   - Syscalls pack `(rc, errno)` into a single 64-bit word (`bit 63 = error`, `bits 62..32 = errno`, `bits 62..0 = value`), decoded in Lean into `SysResult α := Except Errno α`.

4. **Strict TCB & Dependency Hygiene (`c/lean_sys_shim.c ≤ 70 LOC`, `0 import Lean`)**:
   - `lean-sys-core` must link **only** against `libleanrt.a` and standard POSIX `libc` (`supportInterpreter := false`).
   - **Zero `import Lean`**, **zero `libsqlite3`**, **zero `libcurl`/`libssl`**, and **zero parsing or allocation logic in C**. The C shim is restricted to leaf POSIX syscall wrappers (`open`/`flock`, `rename`/`link`, `send`/`write`/`fsync`, `pread`/`read`, `fork`/`setpgid`/`execve`/`waitpid`, `socket`/`bind`/`listen`/`accept4`/`poll`).

5. **Mathlib4 Algebraic Proof Style**:
   Proofs in `LeanSys/Spec.lean` must use concise algebraic idioms (`split <;> simp_all`, `simpa`, `omega`, induction with single-line branches). Verbose `cases <;> cases` trees are forbidden.

6. **LOC & Trust-Surface Ratchet ($\Delta\text{LOC}_{\text{C}} \le 0$)**:
   Every feature addition or optimization must preserve or shrink the C shim footprint (`≤ 70 LOC`) and generalize Layer I combinators in `LeanSys/Spec.lean` rather than accreting ad-hoc parsers or unsafe FFI glue.

---

## 3. Repository Layout & Verification Entrypoints

- **Formal Systems Specifications & 10 C-ABI Gates**: [`LeanSys/Spec.lean`](LeanSys/Spec.lean) (`16/16 non_vacuous_and_tight`)
- **64-Bit Word-Strided Hash (`xxh64Slice`) & 3-Probe Bloom Filter**: [`LeanSys/Hash.lean`](LeanSys/Hash.lean) (`or_and_self`, `bloom_no_false_negative`)
- **Zero-Copy JSON/JSONL Tape Indexer (`JsonTape`)**: [`LeanSys/Codec.lean`](LeanSys/Codec.lean)
- **Leaf POSIX C Shim (`51 LOC`) & Typed FFI**: [`c/lean_sys_shim.c`](c/lean_sys_shim.c), [`LeanSys/Posix.lean`](LeanSys/Posix.lean)
- **Crash-Atomic WAL (`putBatch` Group-Commit) & Hardlinked CAS**: [`LeanSys/Store.lean`](LeanSys/Store.lean)
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
   - `slice_bounds_rejects_overflow`, `wal_frame_rejects_corrupt_or_torn`, `wal_torn_tail_recovers_committed`, `cas_gate_rejects_tampered_or_traversal`, `http_gate_rejects_invalid_envelope`, `fd_lifecycle_rejects_unsafe`.
   - `0 sorryAx`, `0 vacuous` specs (`turbo-lean --json audit-spec LeanSys/Spec.lean`), and `0` forbidden symbols in `nm -u lean-sys-core`.
2. **Layer 2 — Lexicographic Objective (`J_sys`)**:
   - **Primary**: Maximize I/O & RPC throughput geomean $\text{Geomean}(\text{Throughput}_{\text{WAL}}, \text{Throughput}_{\text{CAS}}, \text{Req/s}_{\text{HTTP/IPC}})$ and minimize tail latency $\text{p99}_{\mu\text{s}}$.
   - **Secondary**: Minimize heap allocations per request (`alloc_bytes / op`) and stripped binary size (`< 2.5 MB`).
   - **Resource Envelope**: $\text{LOC}(\text{c/lean\_sys\_shim.c}) \le 70$, $\text{FD}_{\text{leaked}} = 0$, $\text{OrphanProcesses} = 0$, and $\Delta\text{LOC} \le 0$.
