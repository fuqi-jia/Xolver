#!/usr/bin/env bash
# Reproducibly (re)generate the locked UNSAT proof corpus.
#
# Selection criteria (Phase A of the proof implementation plan):
#   * file carries `(set-info :status unsat)`
#   * NOT tagged `:xolver-expected known-fail` / `known-unsound`
#     (we only certify unsats the solver is expected to decide)
#   * the 2 smallest files (by line count) per logic directory, so the
#     corpus stays small (fast external checks, easy debugging) while
#     spanning every supported logic lane.
#
# Run from the repo root. Writes the sorted list to stdout; the committed
# snapshot lives in docs/proof/corpus/UNSAT-CORPUS.txt — regenerate with:
#   bash docs/proof/corpus/select_corpus.sh > docs/proof/corpus/UNSAT-CORPUS.txt
set -euo pipefail

ROOT="${1:-tests/regression}"

for d in "$ROOT"/*/; do
  grep -rl ':status unsat' "$d" --include='*.smt2' 2>/dev/null \
    | { grep -LvE 'placeholder' || true; } \
    | while read -r f; do
        # skip known-fail / known-unsound — no proof obligation for those
        if grep -qE 'xolver-expected[[:space:]]+(known-fail|known-unsound)' "$f"; then
          continue
        fi
        printf '%06d %s\n' "$(wc -l < "$f")" "$f"
      done \
    | sort -n | head -2 | awk '{print $2}'
done
