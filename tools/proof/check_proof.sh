#!/usr/bin/env bash
# Verify Xolver's UNSAT proof for ONE SMT-LIB file with an INDEPENDENT checker.
#
# This is the unsat-side soundness gate: Xolver never grades its own proof — an
# external tool (drat-trim) must accept it. A proof the checker rejects is a
# release blocker, exactly like an unsound verdict.
#
# Usage: check_proof.sh <xolver-bin> <drat-trim-bin> <file.smt2> [workdir]
# Output: one of VERIFIED / REJECTED / NO-PROOF / SKIP, on the file.
# Exit:   0 = unsat AND proof externally VERIFIED
#         1 = unsat but proof REJECTED by the checker      (HARD FAILURE)
#         2 = unsat but NO proof produced (degraded, honest: no false proof)
#         3 = not unsat (sat/unknown) — nothing to certify
set -euo pipefail
XOLVER="${1:?usage: check_proof.sh <xolver> <drat-trim> <file.smt2> [workdir]}"
DRATTRIM="${2:?need drat-trim binary}"
SMT="${3:?need .smt2 file}"
WORK="${4:-$(mktemp -d)}"
mkdir -p "$WORK"
BASE="$WORK/$(basename "$SMT" .smt2)"

verdict="$(ulimit -v 4194304; "$XOLVER" solve "$SMT" --produce-proof "$BASE" 2>/dev/null | tail -1 || true)"

if [ "$verdict" != "unsat" ]; then
  echo "SKIP ($verdict): $SMT"; exit 3
fi
if [ ! -s "$BASE.drat" ] || [ ! -s "$BASE.cnf" ]; then
  # Honest degraded mode: unsat decided outside the SAT core, no certificate.
  echo "NO-PROOF (degraded): $SMT"; exit 2
fi
if "$DRATTRIM" "$BASE.cnf" "$BASE.drat" 2>/dev/null | grep -q 's VERIFIED'; then
  echo "VERIFIED: $SMT"; exit 0
fi
echo "REJECTED (checker refused the proof — HARD FAILURE): $SMT"; exit 1
