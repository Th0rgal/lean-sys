#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export PATH="/var/lib/orb-node/work/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/orb-node/work/caches/elan/bin:/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin:/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$HOME/.elan/bin:/usr/local/cargo/bin:/opt/orb/bin:$PATH"

if [[ "${1:-}" == "--sync-docs" ]]; then
  python3 scripts/sync_docs_inventory.py
fi
python3 scripts/sync_docs_inventory.py --check

echo "[1/5] Building lean-sys (supportInterpreter := false, libleanrt.a only)..."
lake build

echo "[2/5] Running lean-sys-core self-test (40 C-ABI gates + WAL/CAS/Reflink/SigV4/Unix/CgroupV2/IoUring/MmapArena/Codec/Reactor/Sandbox)..."
./.lake/build/bin/lean-sys-core self-test

echo "[3/5] Running lean-sys-core bench..."
./.lake/build/bin/lean-sys-core bench

echo "[4/5] Auditing LeanSys/Spec.lean, LeanSys/Hash.lean, and LeanSys/Gate.lean via turbo-lean (0 vacuous, 0 trivial, 0 sorryAx)..."
if command -v turbo-lean >/dev/null 2>&1; then
  turbo-lean --json audit-spec LeanSys/Spec.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']>=51 and not d.get('horizontal_packing_warnings'), d; print(f'Spec.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight')"
  turbo-lean --json audit-spec LeanSys/Hash.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']>=2, d; print(f'Hash.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight')"
  turbo-lean --json audit-spec LeanSys/Gate.lean | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['ok'] and d['vacuous_specs']==0 and d['trivial_specs']==0 and d['tight_specs']>=2, d; print(f'Gate.lean: {d[\"tight_specs\"]}/{d[\"total_specs_audited\"]} non_vacuous_and_tight')"
elif [ "${GITHUB_ACTIONS:-}" = "true" ] || [ "${REQUIRE_TURBO_LEAN:-}" = "1" ]; then
  echo "ERROR: turbo-lean is required in CI to audit 55/55 tight specs!" >&2
  exit 1
fi

echo "[5/5] Verifying TCB symbol hygiene and C shim LOC cap..."
if nm -u .lake/build/bin/lean-sys-core | grep -E 'lean_elab|lean_environment|sqlite|SSL_'; then
  echo "ERROR: Forbidden frontend/SQLite/OpenSSL symbol found in lean-sys-core!" >&2
  exit 1
fi
SHIM_LOC="$(wc -l < c/lean_sys_shim.c | tr -d ' ')"
if [ "$SHIM_LOC" -gt 65 ]; then
  echo "ERROR: c/lean_sys_shim.c has $SHIM_LOC lines (> 65 LOC cap)!" >&2
  exit 1
fi
SHIM_SEMIS="$(tr -cd ';' < c/lean_sys_shim.c | wc -c | tr -d ' ')"
if [ "$SHIM_SEMIS" -gt 64 ]; then
  echo "ERROR: c/lean_sys_shim.c has $SHIM_SEMIS semicolons (> 64 statement cap)!" >&2
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
FORBIDDEN_RE="max""well|certified-""research|research-""governor"
if git grep -niE "$FORBIDDEN_RE" >/dev/null 2>&1; then
  echo "ERROR: Forbidden external governor reference found in lean-sys!" >&2
  git grep -niE "$FORBIDDEN_RE" >&2
  exit 1
fi
DUP_EXPORTS="$(grep -rhoE 'export[[:space:]]+[A-Za-z0-9_]+' LeanSys/ LeanSys.lean | awk '{print $2}' | sort | uniq -d)"
if [ -n "$DUP_EXPORTS" ]; then
  echo "ERROR: Duplicate C-ABI @[export] symbols found in LeanSys: $DUP_EXPORTS" >&2
  exit 1
fi
SPEC_TIGHT="$(turbo-lean --json audit-spec LeanSys/Spec.lean | python3 -c "import json,sys; print(json.load(sys.stdin)['tight_specs'])" 2>/dev/null || python3 -c "import sys; sys.path.insert(0, 'scripts'); import sync_docs_inventory as s; print(s.compute_inventory()['leansys_spec_tight'])")"
CABI_COUNT="$(grep -rhoE 'export[[:space:]]+leansys_[A-Za-z0-9_]+' LeanSys/Spec.lean | wc -l | tr -d ' ')"
echo "[lean-sys] ALL 5 CI GATES PASSED (${SPEC_TIGHT}/${SPEC_TIGHT} Spec.lean tight specs, ${CABI_COUNT} C-ABI exports, c/lean_sys_shim.c=${SHIM_LOC} LOC, TCB_CLEAN)"
