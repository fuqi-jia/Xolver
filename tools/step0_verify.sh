#!/usr/bin/env bash
# Step 0: re-verify every targeted_eqnia case under full15 (WSL-safe).
# Output TSV: logic  polarity  oracle  xolver  match  secs  key
set -u
WT=/mnt/d/D_Study/BUAA/projects/zolver-eqnia
cd "$WT"
BIN=build/bin/xolver
TIMEOUT="${STEP0_TIMEOUT:-20}"
FULL15="XOLVER_EUF_PROP=1 XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1 XOLVER_ARRAY_CONGR_EXT=1 XOLVER_NRA_LOCALSEARCH=1 XOLVER_PP_SOLVE_EQS=1 XOLVER_PP_SOLVE_EQS_GAUSS=1 XOLVER_LIA_CUTS=1 XOLVER_LIA_GMI_CUTS=1 XOLVER_LIA_INCREMENTAL=1 XOLVER_LRA_INCREMENTAL_BETA=1 XOLVER_NRA_LINEARIZE=1 XOLVER_NIA_MODULAR=1 XOLVER_NRA_CAC_DEADLINE_MS=2000 XOLVER_NIA_FARKAS_OR=1 XOLVER_NRA_INT_PROBE=1 XOLVER_NIA_LBBB=1"
OUT="${STEP0_OUT:-/tmp/eqnia_step0.tsv}"
: > "$OUT"
printf 'logic\tpolarity\toracle\txolver\tmatch\tsecs\tkey\n' >> "$OUT"
n=0
# skip header line of MANIFEST
tail -n +2 targeted_eqnia/MANIFEST.tsv | while IFS=$'\t' read -r logic category polarity size oracle xwas key; do
  [ -z "${key:-}" ] && continue
  f="targeted_eqnia/$key"
  [ -f "$f" ] || { printf '%s\t%s\t%s\tMISSING\t-\t0\t%s\n' "$logic" "$polarity" "$oracle" "$key" >> "$OUT"; continue; }
  t0=$(date +%s)
  v=$( ulimit -v 4000000; env $FULL15 timeout "$TIMEOUT" "$BIN" solve "$f" 2>/dev/null | tr -d '[:space:]' )
  rc=$?
  t1=$(date +%s)
  secs=$((t1 - t0))
  if [ $rc -eq 124 ]; then v="timeout"; fi
  if [ $rc -ge 128 ]; then v="crash:rc$rc"; fi
  [ -z "$v" ] && v="empty:rc$rc"
  m="-"
  case "$v" in
    sat|unsat) [ "$v" = "$oracle" ] && m="SOLVE" || m="WRONG" ;;
    *) m="miss" ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$logic" "$polarity" "$oracle" "$v" "$m" "$secs" "$key" >> "$OUT"
  n=$((n+1))
done
echo "STEP0_DONE n=$n out=$OUT" >> "$OUT"
