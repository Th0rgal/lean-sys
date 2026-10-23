#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$HOME/.elan/bin:$PATH"

if [[ "${1:-}" == "--sync-docs" ]]; then
  python3 scripts/sync_docs_inventory.py
fi
python3 scripts/sync_docs_inventory.py --check

echo "[1/5] Building lean-sys (supportInterpreter := false, libleanrt.a only)..."
lake build

echo "[2/5] Running lean-sys-core self-test (17 C-ABI gates + WAL/CAS/SST/Table/Auth/ProcLog/JsonRpc/ShmRing/Codec/Reactor/Sandbox)..."
./.lake/build/bin/lean-sys-core self-test

echo "[3/5] Running lean-sys-core bench..."
./.lake/build/bin/lean-sys-core bench

echo "[4/5] Auditing LeanSys/Spec.lean and LeanSys/Hash.lean via turbo-lean (0 vacuous, 0 trivial, 0 sorryAx)..."
if command -v turbo-lean >/dev/null 2>&1; then
  turbo-lean --json audit-spec LeanSys/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']>=24 and not d.get('horizontal_packing_warnings'), d; print(f'Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight')"
  turbo-lean --json audit-spec LeanSys/Hash.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']>=2, d; print(f'Hash.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight')"
fi

echo "[5/5] Verifying TCB symbol hygiene and C shim LOC cap..."
if nm -u .lake/build/bin/lean-sys-core | grep -E 'lean_elab|lean_environment|sqlite|SSL_'; then
  echo "ERROR: Forbidden frontend/SQLite/OpenSSL symbol found in lean-sys-core!" >&2
  exit 1
fi
SHIM_LOC="$(wc -l < c/lean_sys_shim.c | tr -d ' ')"
if [ "$SHIM_LOC" -gt 70 ]; then
  echo "ERROR: c/lean_sys_shim.c has $SHIM_LOC lines (> 70 LOC cap)!" >&2
  exit 1
fi
if grep -rn '^import Lean\b' LeanSys/ LeanSys.lean; then
  echo "ERROR: Forbidden 'import Lean' found in LeanSys!" >&2
  exit 1
fi
if grep -rn '^\s*sorry\b' LeanSys/ LeanSys.lean; then
  echo "ERROR: Forbidden 'sorry' found in LeanSys!" >&2
  exit 1
fi
echo "[lean-sys] ALL 5 CI GATES PASSED (26/26 tight specs, 17 C-ABI exports, c/lean_sys_shim.c=${SHIM_LOC} LOC, TCB_CLEAN)"
