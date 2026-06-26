#!/usr/bin/env bash
# Verify Xolver's UNSAT proof for ONE SMT-LIB file with an INDEPENDENT checker.
#
# This is the unsat-side soundness gate: Xolver never grades its own proof — an
# external tool (drat-trim) must accept it. A proof the checker rejects is a
# release blocker, exactly like an unsound verdict.
#
# Usage: check_proof.sh <xolver-bin> <drat-trim-bin> <file.smt2> [workdir] [carcara-bin]
# Output: one of VERIFIED / VERIFIED-SKELETON / REJECTED / NO-PROOF / SKIP.
# Exit:   0 = unsat AND proof externally VERIFIED
#         1 = unsat but proof REJECTED by the checker      (HARD FAILURE)
#         2 = unsat but NO proof produced (degraded, honest: no false proof)
#         3 = not unsat (sat/unknown) — nothing to certify
set -euo pipefail
XOLVER="${1:?usage: check_proof.sh <xolver> <drat-trim> <file.smt2> [workdir] [carcara]}"
DRATTRIM="${2:?need drat-trim binary}"
SMT="${3:?need .smt2 file}"
WORK="${4:-$(mktemp -d)}"
CARCARA="${5:-}"
mkdir -p "$WORK"
BASE="$WORK/$(basename "$SMT" .smt2)"

verdict="$(ulimit -v 4194304; "$XOLVER" solve "$SMT" --produce-proof "$BASE" 2>/dev/null | tail -1 || true)"

if [ "$verdict" != "unsat" ]; then
  echo "SKIP ($verdict): $SMT"; exit 3
fi

# Phase C: prefer a complete Alethe THEORY proof when present — it is checked by
# Carcara against the ORIGINAL problem and certifies the theory reasoning too (not
# just the Boolean skeleton). A rejected Alethe is a HARD FAILURE.
# The Alethe proof references post-normalization IR atoms, so it is checked
# against the IR-derived problem Xolver emits (<base>.smt2), not the original —
# the original->IR normalization is trusted preprocessing (Phase D obligation).
if [ -n "$CARCARA" ] && [ -s "$BASE.alethe" ] && [ -s "$BASE.smt2" ]; then
  if "$CARCARA" check "$BASE.alethe" "$BASE.smt2" 2>/dev/null | grep -q '^valid'; then
    echo "VERIFIED (alethe/carcara): $SMT"; exit 0
  fi
  echo "REJECTED (carcara refused the Alethe proof — HARD FAILURE): $SMT"; exit 1
fi
if [ ! -s "$BASE.drat" ] || [ ! -s "$BASE.cnf" ]; then
  # Honest degraded mode: unsat decided outside the SAT core, no certificate.
  echo "NO-PROOF (degraded): $SMT"; exit 2
fi
if "$DRATTRIM" "$BASE.cnf" "$BASE.drat" 2>/dev/null | grep -q 's VERIFIED'; then
  # Honesty: a proof that assumed theory lemmas as axioms certifies the Boolean
  # skeleton only (lemmas justified in Phase C); report it distinctly so a
  # skeleton is never read as a full soundness certificate.
  assumed="$(sed -n 's/^c xolver-proof:.* \([0-9][0-9]*\) theory lemmas assumed.*/\1/p' "$BASE.cnf" | head -1)"
  if [ -n "$assumed" ] && [ "$assumed" -gt 0 ] 2>/dev/null; then
    echo "VERIFIED-SKELETON ($assumed lemmas assumed): $SMT"; exit 0
  fi
  echo "VERIFIED: $SMT"; exit 0
fi
echo "REJECTED (checker refused the proof — HARD FAILURE): $SMT"; exit 1
