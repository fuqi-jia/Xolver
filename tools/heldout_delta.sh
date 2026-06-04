#!/usr/bin/env bash
# Compare two heldout_validate.sh outputs and report delta wins.
# Usage: tools/heldout_delta.sh <before.tsv> <after.tsv>
set -u
B=${1?before.tsv}
A=${2?after.tsv}

echo "=== histogram BEFORE ==="
awk -F'\t' 'NR>1 {h[$4]++} END {for(k in h) printf "  %-15s %d\n", k, h[k]}' "$B"
echo "=== histogram AFTER ==="
awk -F'\t' 'NR>1 {h[$4]++} END {for(k in h) printf "  %-15s %d\n", k, h[k]}' "$A"

echo "=== per-case verdict change ==="
join -t $'\t' -1 2 -2 2 \
  <(awk -F'\t' 'NR>1 {print $2"\t"$4"\t"$6}' "$B" | sort) \
  <(awk -F'\t' 'NR>1 {print $2"\t"$4"\t"$6}' "$A" | sort) \
  | awk -F'\t' '{printf "  %s  %s/%sms  ->  %s/%sms  %s\n", $1, $2, $3, $4, $5, ($2!=$4 ? "  ★" : "")}' | sed 's|targeted_nia/QF_NIA/||'

echo "=== wins (verdict moved into sat) ==="
join -t $'\t' -1 2 -2 2 \
  <(awk -F'\t' 'NR>1 {print $2"\t"$4}' "$B" | sort) \
  <(awk -F'\t' 'NR>1 {print $2"\t"$4}' "$A" | sort) \
  | awk -F'\t' '$2!="sat" && $3=="sat" {print "  ★ "$1}' | sed 's|targeted_nia/QF_NIA/||'

echo "=== regressions (verdict moved out of sat) ==="
join -t $'\t' -1 2 -2 2 \
  <(awk -F'\t' 'NR>1 {print $2"\t"$4}' "$B" | sort) \
  <(awk -F'\t' 'NR>1 {print $2"\t"$4}' "$A" | sort) \
  | awk -F'\t' '$2=="sat" && $3!="sat" {print "  ✗ "$1}' | sed 's|targeted_nia/QF_NIA/||'
