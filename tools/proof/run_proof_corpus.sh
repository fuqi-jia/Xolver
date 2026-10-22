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
XOLVER="${1:?usage: run_proof_corpus.sh <xolver> <drat-trim> <corpus-list> [carcara]}"
DRATTRIM="${2:?need drat-trim binary}"
LIST="${3:?need corpus list file}"
CARCARA="${4:-}"   # optional: also check Alethe theory proofs with Carcara
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${XOLVER_PROOF_WORKDIR:-$(mktemp -d)}"
mkdir -p "$WORK"
[ -r "$LIST" ] || { echo "ERROR: cannot read $LIST"; exit 1; }
echo "Proof artifacts: $WORK"

v=0 skel=0 rej=0 nop=0 skip=0 errors=0 cases=0 rejected_files=""
while IFS= read -r f; do
  [ -z "$f" ] && continue
  [[ "$f" = \#* ]] && continue
  cases=$((cases+1))
  [ -f "$f" ] || { echo "MISSING: $f"; errors=$((errors+1)); continue; }
  casework="$(mktemp -d "$WORK/case.XXXXXXXX")"
  out="$(bash "$HERE/check_proof.sh" "$XOLVER" "$DRATTRIM" "$f" "$casework" "$CARCARA" 2>&1)"
  rc=$?
  echo "$out"
  case $rc in
    0) case "$out" in *VERIFIED-SKELETON*) skel=$((skel+1));; *) v=$((v+1));; esac;;
    1) rej=$((rej+1)); rejected_files="$rejected_files
  $f";;
    2) nop=$((nop+1));;
    3) skip=$((skip+1));;
    *) errors=$((errors+1));;
  esac
done < "$LIST"

echo "----------------------------------------------------------------"
echo "VERIFIED(complete)=$v  VERIFIED-SKELETON(lemmas assumed)=$skel  NO-PROOF(degraded)=$nop  SKIP(not-unsat)=$skip  REJECTED=$rej ERROR=$errors"
if [ "$rej" -ne 0 ] || [ "$errors" -ne 0 ] || [ "$cases" -eq 0 ]; then
  echo "HARD FAILURE: $rej rejected proofs, $errors execution/setup errors, $cases cases:$rejected_files"
  exit 1
fi
echo "OK: no rejected artifacts or execution errors; complete/skeleton/no-proof coverage reported separately."
exit 0
