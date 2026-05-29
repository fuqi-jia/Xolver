#!/usr/bin/env bash
# =============================================================================
# rerun_diff.sh — turnkey per-node authoritative differential (no z3 re-run).
#
# The diff_*.csv candidate columns go stale whenever the binary changes (e.g.
# pre-f58ed43 NIA, pre-EQNA-fix UFNIA). This re-runs Xolver baseline (floors) +
# candidate (floors+flags) on the cached-oracle key set at the competition budget,
# then JOINS the cached z3 verdict into a fresh diff_<logic>_node<i>.csv. It never
# re-runs z3 — the oracle is read from the z3_*.csv cache.
#
# Usage (per node):
#   tools/rerun_diff.sh <logic> <node> <total_nodes> [candidate_flag_csv]
# e.g. on 3 nodes for QF_NIA with the modular lever:
#   tools/rerun_diff.sh QF_NIA 1 3 XOLVER_NIA_MODULAR     # panda1
#   tools/rerun_diff.sh QF_NIA 2 3 XOLVER_NIA_MODULAR     # panda2
#   tools/rerun_diff.sh QF_NIA 3 3 XOLVER_NIA_MODULAR     # panda3
#
# Env overrides: BIN BENCH T(imeout, default 1200) J(obs) MEMCAP_KB(default 30GB)
#                Z3(cache glob) OUT
# Competition budget: T=1200, MEMCAP_KB~30GB, high J — this is panda, not WSL.
# =============================================================================
set -euo pipefail

LOGIC="${1:?usage: rerun_diff.sh <logic> <node> <total_nodes> [flag_csv]}"
NODE="${2:?node index (1..total)}"
TOTAL="${3:?total nodes}"
FLAGS="${4:-XOLVER_NIA_MODULAR}"

HERE="$(cd "$(dirname "$0")/.." && pwd)"        # repo root (tools/..)
BIN="${BIN:-$HERE/bin/xolver}"
BENCH="${BENCH:-$HERE/benchmark/non-incremental}"
T="${T:-1200}"
J="${J:-$(nproc 2>/dev/null || echo 8)}"
MEMCAP_KB="${MEMCAP_KB:-30000000}"               # ~30 GB, the retuned per-proc cap
Z3="${Z3:-$HERE/results/z3_${LOGIC}_node*.csv}"
OUT="${OUT:-$HERE/results/diff_${LOGIC}_node${NODE}.csv}"

# Soundness floors pinned ON in BOTH baseline and candidate (the search only adds
# completeness flags on top; floors never drop).
FLOORS="XOLVER_PP_STRICT_VALIDATION=1 XOLVER_PP_VALIDATE_NONLINEAR_SAT=1 \
XOLVER_SAT_DEFER_EARLY_CONFLICT=1 XOLVER_COMB_SAT_FLOOR=1 XOLVER_NRA_UNSAT_CERT=1"
# candidate = floors + each requested flag =1
CAND_ENV="$(printf '%s\n' "${FLAGS//,/ }" | tr ' ' '\n' | sed '/^$/d;s/$/=1/' | tr '\n' ' ')"

echo "BIN=$BIN  LOGIC=$LOGIC  node $NODE/$TOTAL  T=${T}s  J=$J  memcap=${MEMCAP_KB}KB"
echo "candidate flags: $FLAGS"
[ -x "$BIN" ] || { echo "ERROR: solver not executable: $BIN"; exit 1; }

# 1. node key set: cached-oracle keys, round-robin sliced (deterministic, no overlap/gap)
LIST="$(mktemp)"
# shellcheck disable=SC2086
tail -q -n +2 $Z3 2>/dev/null | cut -d, -f1 | LC_ALL=C sort -u \
  | awk -v N="$TOTAL" -v i="$NODE" 'NR % N == (i-1)' > "$LIST"
KEYS="$(wc -l < "$LIST")"
echo "node key set: $KEYS files (from z3 cache $Z3)"
[ "$KEYS" -gt 0 ] || { echo "ERROR: 0 keys (check Z3 cache / node split)"; rm -f "$LIST"; exit 1; }

BASE_DIR="$(mktemp -d)"; CAND_DIR="$(mktemp -d)"
RB="$HERE/tools/run_benchmark.py"

run_cfg() {  # $1=label $2=outdir $3=extra-env
  echo "[$1] solving $KEYS files @ ${T}s ..."
  # shellcheck disable=SC2086
  ( ulimit -v "$MEMCAP_KB" 2>/dev/null || true
    env $FLOORS $3 python3 "$RB" --solver "$BIN" --logic "$LOGIC" \
        --benchmark-dir "$BENCH" --file-list "$LIST" -t "$T" -j "$J" -o "$2" )
}

# 2. baseline (floors only)   3. candidate (floors + flags)
run_cfg baseline  "$BASE_DIR" ""
run_cfg candidate "$CAND_DIR" "$CAND_ENV"

# 4. join the cached z3 oracle -> fresh diff_<logic>_node<i>.csv (no z3 re-run)
python3 -m eval.make_diff --baseline-run "$BASE_DIR" --candidate-run "$CAND_DIR" \
    --oracle "$Z3" --out "$OUT"

rm -f "$LIST"
echo "=== done: $OUT  (score with: python3 -m eval.diffreport --diff '$OUT' --blan 'results/blan_${LOGIC}_node*.csv') ==="
