#!/usr/bin/env bash
# Run the UNSAT-proof gate over a corpus of SMT-LIB files and summarize.
#
# The soundness contract (CLAUDE.md + the proof plan):
#   * REJECTED (checker refused a produced proof) is a HARD FAILURE — a wrong
#     proof is a release blocker. Any REJECTED makes this script exit non-zero.
#   * NO-PROOF (degraded: unsat with no certificate) is ALLOWED and only counted,
#     never a failure — we never emit a false proof to avoid the degraded path.
#   * VERIFIED is the win; SKIP (not unsat) is ignored.
#
# Usage: run_proof_corpus.sh <xolver-bin> <drat-trim-bin> <corpus-list-file>
#   corpus-list-file: one path to a .smt2 per line (e.g. docs/proof/corpus/UNSAT-CORPUS.txt)
set -uo pipefail
XOLVER="${1:?usage: run_proof_corpus.sh <xolver> <drat-trim> <corpus-list>}"
DRATTRIM="${2:?need drat-trim binary}"
LIST="${3:?need corpus list file}"
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

v=0 rej=0 nop=0 skip=0 rejected_files=""
while IFS= read -r f; do
  [ -z "$f" ] && continue
  [ -f "$f" ] || { echo "MISSING: $f"; continue; }
  out="$(bash "$HERE/check_proof.sh" "$XOLVER" "$DRATTRIM" "$f" "$WORK" 2>/dev/null)"
  rc=$?
  echo "$out"
  case $rc in
    0) v=$((v+1));;
    1) rej=$((rej+1)); rejected_files="$rejected_files
  $f";;
    2) nop=$((nop+1));;
    3) skip=$((skip+1));;
  esac
done < "$LIST"

echo "----------------------------------------------------------------"
echo "VERIFIED=$v  NO-PROOF(degraded)=$nop  SKIP(not-unsat)=$skip  REJECTED=$rej"
if [ "$rej" -ne 0 ]; then
  echo "HARD FAILURE: $rej proof(s) REJECTED by the external checker:$rejected_files"
  exit 1
fi
echo "OK: no rejected proofs (every produced proof externally verified)."
exit 0
