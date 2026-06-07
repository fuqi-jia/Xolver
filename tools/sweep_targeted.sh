#!/usr/bin/env bash
# Full targeted_eqnia sweep: solve every case, compare to expected polarity,
# tally per division. WSL-safe: ulimit + per-case timeout, sequential.
set -u
cd "$(dirname "$0")/.."
BIN=build/bin/xolver
TO=${1:-25}
MAN=targeted_eqnia/MANIFEST.tsv
declare -A solved tot
total_solve=0; total_all=0
while IFS=$'\t' read -r logic cat pol size oracle xolwas key; do
  [ "$logic" = "logic" ] && continue
  ff="targeted_eqnia/$key"; [ -f "$ff" ] || continue
  tot[$logic]=$(( ${tot[$logic]:-0} + 1 )); total_all=$((total_all+1))
  o=$( ulimit -v 8000000; timeout "$TO" "$BIN" solve "$ff" 2>/dev/null | tail -1 )
  if [ "$o" = "$pol" ]; then
    solved[$logic]=$(( ${solved[$logic]:-0} + 1 )); total_solve=$((total_solve+1))
    echo "  SOLVED($o) $logic $(basename "$key" | cut -c1-40)"
  fi
done < "$MAN"
echo "============================================================"
for l in QF_UFNIA QF_ANIA QF_AUFNIA QF_UFDTNIA; do
  echo "  $l: ${solved[$l]:-0}/${tot[$l]:-0} solved"
done
echo "  TOTAL: $total_solve/$total_all"
