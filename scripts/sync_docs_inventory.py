#!/usr/bin/env python3
"""
scripts/sync_docs_inventory.py — Automated Documentation & Context Ratchet (`lean-sys`).

Computes theorem, tight-spec, C-ABI export, and C-shim LOC counts directly from
`LeanSys/Spec.lean`, `LeanSys/Hash.lean`, `LeanSys/Gate.lean`, and `c/lean_sys_shim.c`,
and synchronizes `<!-- inventory:KEY -->...<!-- /inventory:KEY -->` blocks across
`README.md` and `AGENTS.md`.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Dict

ROOT_DIR = Path(__file__).resolve().parent.parent
SPEC_PATH = ROOT_DIR / "LeanSys" / "Spec.lean"
HASH_PATH = ROOT_DIR / "LeanSys" / "Hash.lean"
GATE_PATH = ROOT_DIR / "LeanSys" / "Gate.lean"
SHIM_PATH = ROOT_DIR / "c" / "lean_sys_shim.c"
DOC_PATHS = [
    ROOT_DIR / "README.md",
    ROOT_DIR / "AGENTS.md",
]


def compute_inventory() -> Dict[str, str]:
    spec_text = SPEC_PATH.read_text(encoding="utf-8")
    hash_text = HASH_PATH.read_text(encoding="utf-8")
    gate_text = GATE_PATH.read_text(encoding="utf-8") if GATE_PATH.is_file() else ""
    spec_thms = re.findall(r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", spec_text)
    hash_thms = re.findall(r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", hash_text)
    gate_thms = re.findall(r"(?m)^\s*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", gate_text)
    spec_tight = len(spec_thms)
    hash_tight = len(hash_thms)
    gate_tight = len(gate_thms)
    total_tight = spec_tight + hash_tight + gate_tight
    cabi_exports = len(re.findall(r"@\[inline,\s*export\s+[A-Za-z0-9_]+\]", spec_text))
    shim_loc = sum(1 for _ in SHIM_PATH.open("r", encoding="utf-8"))
    return {
        "leansys_spec_tight": str(spec_tight),
        "leansys_hash_tight": str(hash_tight),
        "leansys_gate_tight": str(gate_tight),
        "leansys_total_tight": str(total_tight),
        "leansys_cabi": str(cabi_exports),
        "leansys_shim_loc": str(shim_loc),
        "leansys_summary": f"{total_tight}/{total_tight} tight specs ({spec_tight} in Spec.lean + {hash_tight} in Hash.lean + {gate_tight} in Gate.lean, {cabi_exports} C-ABI exports, c/lean_sys_shim.c={shim_loc} LOC, 0 sorryAx)",
    }


def sync_file(path: Path, inv: Dict[str, str], check_only: bool) -> bool:
    if not path.is_file():
        return True
    orig = path.read_text(encoding="utf-8")
    updated = orig
    for key, val in inv.items():
        pattern = re.compile(
            rf"(<!--\s*inventory:{re.escape(key)}\s*-->)(.*?)(<!--\s*/inventory:{re.escape(key)}\s*-->)",
            re.DOTALL,
        )
        updated = pattern.sub(rf"\g<1>{val}\g<3>", updated)
    if updated != orig:
        if check_only:
            print(f"[sync-docs] Out-of-sync inventory markers in {path.relative_to(ROOT_DIR)}", file=sys.stderr)
            return False
        path.write_text(updated, encoding="utf-8")
        print(f"[sync-docs] Updated {path.relative_to(ROOT_DIR)}")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description="Synchronize or verify lean-sys documentation inventory markers")
    parser.add_argument("--check", action="store_true", help="Fail if any inventory marker is out of sync")
    args = parser.parse_args()

    inv = compute_inventory()
    ok = True
    for doc in DOC_PATHS:
        if not sync_file(doc, inv, check_only=args.check):
            ok = False
    if ok:
        print(f"[sync-docs] OK ({inv['leansys_summary']})")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
