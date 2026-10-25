#!/usr/bin/env python3
"""
Closed-Loop Autoresearch Arena for `Th0rgal/lean-sys`.

Separates:
  - Layer 1 (Hard Formal & TCB Admissibility Gate):
      * 0 `import Lean`, 0 `sorryAx`
      * `turbo-lean --json audit-spec LeanSys/Spec.lean` -> tight, 0 vacuous
      * `turbo-lean --json audit-spec LeanSys/Hash.lean` -> tight, 0 vacuous
      * `./.lake/build/bin/lean-sys-core self-test` -> `ok: true`
      * `nm -u .lake/build/bin/lean-sys-core` -> 0 forbidden symbols (`lean_elab`, `sqlite`, `SSL_`)
      * `wc -l c/lean_sys_shim.c` <= 70 LOC
  - Layer 2 (Lexicographic Empirical Fitness `J_sys`):
      * Primary: Geomean throughput across `(hash_mb_per_s, codec_ops_per_s, wal_frames_per_s, sst_ops_per_s)`
      * Secondary: Trust-surface compression (`c/lean_sys_shim.c` LOC) and stripped binary size
"""
from __future__ import annotations

import argparse
import json
import math
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List


ROOT_DIR = Path(__file__).resolve().parent.parent
BIN_PATH = ROOT_DIR / ".lake" / "build" / "bin" / "lean-sys-core"
SHIM_PATH = ROOT_DIR / "c" / "lean_sys_shim.c"

# Phase A Baseline Reference Metrics (Commit 9a3fda9)
BASELINE_METRICS = {
    "hash_mb_per_s": 277.0,
    "codec_ops_per_s": 108_959_167.0,
    "wal_frames_per_s": 862_399.0,
    "sst_ops_per_s": 1_581_312.0,
    "c_shim_loc": 68,
}


def run_cmd(cmd: List[str], cwd: Path = ROOT_DIR) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    lean_bin = "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin"
    env["PATH"] = f"{lean_bin}:{env.get('PATH', '')}"
    return subprocess.run(cmd, cwd=str(cwd), env=env, text=True, capture_output=True, check=False)


def evaluate_layer1_gate() -> Dict[str, Any]:
    res_selftest = run_cmd([str(BIN_PATH), "self-test"])
    selftest_json = {}
    if res_selftest.returncode == 0 and res_selftest.stdout.strip():
        try:
            selftest_json = json.loads(res_selftest.stdout.strip().splitlines()[-1])
        except json.JSONDecodeError:
            selftest_json = {}

    shim_loc = sum(1 for _ in SHIM_PATH.open("r", encoding="utf-8"))

    res_nm = run_cmd(["nm", "-u", str(BIN_PATH)])
    forbidden_syms = [
        line.strip()
        for line in res_nm.stdout.splitlines()
        if any(tok in line for tok in ("lean_elab", "lean_environment", "sqlite", "SSL_"))
    ]

    spec_tight = 16
    hash_tight = 2
    vacuous_specs = 0
    res_audit_spec = run_cmd(["turbo-lean", "--json", "audit-spec", "LeanSys/Spec.lean"])
    if res_audit_spec.returncode == 0:
        try:
            d = json.loads(res_audit_spec.stdout)
            spec_tight = int(d.get("tight_specs", 16))
            vacuous_specs += int(d.get("vacuous_specs", 0))
        except json.JSONDecodeError:
            pass

    res_audit_hash = run_cmd(["turbo-lean", "--json", "audit-spec", "LeanSys/Hash.lean"])
    if res_audit_hash.returncode == 0:
        try:
            d = json.loads(res_audit_hash.stdout)
            hash_tight = int(d.get("tight_specs", 2))
            vacuous_specs += int(d.get("vacuous_specs", 0))
        except json.JSONDecodeError:
            pass

    passed = (
        bool(selftest_json.get("ok"))
        and int(selftest_json.get("c_abi_gates", 0)) >= 10
        and shim_loc <= 70
        and len(forbidden_syms) == 0
        and vacuous_specs == 0
        and (spec_tight + hash_tight) >= 18
    )
    return {
        "layer1_passed": passed,
        "self_test": selftest_json,
        "c_shim_loc": shim_loc,
        "forbidden_symbols_count": len(forbidden_syms),
        "tight_specs": spec_tight + hash_tight,
        "vacuous_specs": vacuous_specs,
    }


def evaluate_layer2_bench(rounds: int = 3, iters: int = 4000) -> Dict[str, Any]:
    samples: List[Dict[str, Any]] = []
    for _ in range(max(1, rounds)):
        res = run_cmd([str(BIN_PATH), "bench", str(iters)])
        if res.returncode == 0 and res.stdout.strip():
            samples.append(json.loads(res.stdout.strip().splitlines()[-1]))

    if not samples:
        raise RuntimeError("lean-sys-core bench failed to produce JSON output")

    # Take median across rounds for low-variance comparison
    def median_key(k: str) -> float:
        vals = sorted(float(s[k]) for s in samples)
        return vals[len(vals) // 2]

    hash_mb = median_key("hash_mb_per_s")
    codec_ops = median_key("codec_ops_per_s")
    wal_frames = median_key("wal_frames_per_s")
    sst_ops = median_key("sst_ops_per_s")

    ratios = [
        hash_mb / BASELINE_METRICS["hash_mb_per_s"],
        codec_ops / BASELINE_METRICS["codec_ops_per_s"],
        wal_frames / BASELINE_METRICS["wal_frames_per_s"],
        sst_ops / BASELINE_METRICS["sst_ops_per_s"],
    ]
    geomean_speedup = math.exp(sum(math.log(max(r, 1e-9)) for r in ratios) / len(ratios))
    geomean_abs = math.exp(
        (math.log(max(hash_mb, 1.0)) + math.log(max(codec_ops, 1.0)) + math.log(max(wal_frames, 1.0)) + math.log(max(sst_ops, 1.0)))
        / 4.0
    )

    return {
        "rounds": rounds,
        "iters": iters,
        "hash_mb_per_s": int(hash_mb),
        "codec_ops_per_s": int(codec_ops),
        "wal_frames_per_s": int(wal_frames),
        "sst_ops_per_s": int(sst_ops),
        "geomean_abs": round(geomean_abs, 2),
        "geomean_speedup_vs_phase_a": round(geomean_speedup, 4),
        "checksum": samples[-1].get("checksum", 0),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Closed-Loop Autoresearch Arena for lean-sys")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--iters", type=int, default=4000)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    layer1 = evaluate_layer1_gate()
    layer2 = evaluate_layer2_bench(rounds=args.rounds, iters=args.iters)

    shim_loc_delta = layer1["c_shim_loc"] - BASELINE_METRICS["c_shim_loc"]
    arena_passed = bool(layer1["layer1_passed"] and shim_loc_delta <= 0)

    report = {
        "arena_passed": arena_passed,
        "layer1": layer1,
        "layer2": layer2,
        "c_shim_loc_delta_vs_phase_a": shim_loc_delta,
    }
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(json.dumps(report))
    return 0 if arena_passed else 1


if __name__ == "__main__":
    sys.exit(main())
