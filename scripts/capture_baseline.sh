#!/usr/bin/env bash
#
# capture_baseline.sh — record a per-file verdict manifest over the regression
# corpus, for the "0-unsound + zero decided-count delta" gate that every
# behavior-neutral refactor phase must pass (see the flag-refactor plan).
#
# Run it ONCE on the pristine tree (Phase 0) to lock the reference, then re-run
# after each phase and `diff` the manifest: any file whose verdict changed is a
# regression to investigate (a sat/unsat that flipped, or a decided case that
# became unknown/timeout). A clean diff == zero decided-count delta.
#
# Usage: scripts/capture_baseline.sh [out.tsv] [timeout_seconds]
#   defaults: docs/flags/baseline-verdicts.tsv , 20s per case
#
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

OUT="${1:-docs/flags/baseline-verdicts.tsv}"
TIMEOUT="${2:-20}"
SOLVER="build/bin/xolver"
CORPUS="tests/regression"

if [ ! -x "$SOLVER" ]; then
  echo "ERROR: $SOLVER not built. Build first:" >&2
  echo "  git submodule update --init --recursive" >&2
  echo "  cmake -S . -B build && cmake --build build -j2" >&2
  exit 1
fi

mkdir -p "$(dirname "$OUT")"
: > "$OUT.tmp"

n=0
while IFS= read -r f; do
  rel="${f#./}"
  # Non-verbose: xolver prints exactly sat/unsat/unknown on stdout.
  v="$(timeout "$TIMEOUT" "$SOLVER" solve "$rel" 2>/dev/null | tr -d '[:space:]' || true)"
  case "$v" in
    sat|unsat|unknown) : ;;
    "")  v="timeout" ;;
    *)   v="error:$v" ;;
  esac
  printf '%s\t%s\n' "$rel" "$v" >> "$OUT.tmp"
  n=$((n+1))
done < <(find "$CORPUS" -name '*.smt2' | sort)

sort "$OUT.tmp" > "$OUT"
rm -f "$OUT.tmp"

# Summary
{
  echo "=== baseline verdicts ==="
  echo "cases:   $n"
  for k in sat unsat unknown timeout; do
    c=$(awk -F'\t' -v k="$k" '$2==k' "$OUT" | grep -c . || true)
    echo "$k: $c"
  done
  e=$(awk -F'\t' '$2 ~ /^error/' "$OUT" | grep -c . || true)
  echo "error: $e"
  echo "decided (sat+unsat): $(awk -F'\t' '$2=="sat"||$2=="unsat"' "$OUT" | grep -c . || true)"
  echo "written: $OUT"
} >&2
