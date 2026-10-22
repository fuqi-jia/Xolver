#!/usr/bin/env bash
# Verify Xolver's UNSAT proof for ONE SMT-LIB file with an INDEPENDENT checker.
#
# This is the unsat-side soundness gate: Xolver never grades its own proof — an
# external tool (drat-trim) must accept it. A proof the checker rejects is a
# release blocker, exactly like an unsound verdict.
#
# Usage: check_proof.sh <xolver-bin> <drat-trim-bin> <file.smt2> [workdir] [carcara-bin]
# Output: one of VERIFIED / VERIFIED-SKELETON / REJECTED / NO-PROOF / SKIP.
# Exit:   0 = proof artifact accepted; read VERIFIED vs VERIFIED-SKELETON
#         1 = unsat but proof REJECTED by the checker      (HARD FAILURE)
#         2 = unsat but NO proof produced (degraded, honest: no false proof)
#         3 = not unsat (sat/unknown) — nothing to certify
#         4 = solver execution/setup error (always a hard failure)
set -euo pipefail
XOLVER="${1:?usage: check_proof.sh <xolver> <drat-trim> <file.smt2> [workdir] [carcara]}"
DRATTRIM="${2:?need drat-trim binary}"
SMT="${3:?need .smt2 file}"
WORK="${4:-$(mktemp -d)}"
CARCARA="${5:-}"
mkdir -p "$WORK"
BASE="$WORK/$(basename "$SMT" .smt2)"

if (ulimit -v 4194304; timeout "${XOLVER_PROOF_TIMEOUT:-300}" \
    "$XOLVER" solve "$SMT" --produce-proof "$BASE") > "$BASE.stdout" 2> "$BASE.stderr"; then
  solve_rc=0
else
  solve_rc=$?
fi
if [ "$solve_rc" -ne 0 ]; then
  echo "ERROR (solver exit=$solve_rc): $SMT"; exit 4
fi
verdict="$(sed -n -E 's/^(sat|unsat|unknown)[[:space:]]*$/\1/p' "$BASE.stdout" | tail -1)"
if [ -z "$verdict" ]; then
  echo "ERROR (no solver verdict): $SMT"; exit 4
fi
expected="$(sed -n -E 's/;.*//; s/.*\(set-info[[:space:]]+:status[[:space:]]+(sat|unsat)\).*/\1/p' "$SMT" | head -1)"
if { [ "$expected" = unsat ] && [ "$verdict" = sat ]; } || \
   { [ "$expected" = sat ] && [ "$verdict" = unsat ]; }; then
  echo "REJECTED (opposite verdict: expected=$expected actual=$verdict): $SMT"; exit 1
fi

if [ "$verdict" != "unsat" ]; then
  echo "SKIP ($verdict): $SMT"; exit 3
fi

# Prefer an Alethe theory proof when present. A rejected proof is a hard failure.
# The Alethe proof references post-normalization IR atoms, so it is checked
# against the IR-derived problem Xolver emits (<base>.smt2), not the original —
# the original->IR normalization is trusted preprocessing (Phase D obligation).
if [ -n "$CARCARA" ] && [ -s "$BASE.alethe" ] && [ -s "$BASE.smt2" ]; then
  if "$CARCARA" check "$BASE.alethe" "$BASE.smt2" > "$BASE.carcara-output" 2>&1 && \
      grep -Eq '^[[:space:]]*valid[[:space:]]*$' "$BASE.carcara-output"; then
    echo "VERIFIED (alethe/carcara): $SMT"; exit 0
  fi
  echo "REJECTED (carcara refused the Alethe proof — HARD FAILURE): $SMT"; exit 1
fi
if [ ! -s "$BASE.drat" ] || [ ! -s "$BASE.cnf" ]; then
  # Honest degraded mode: unsat decided outside the SAT core, no certificate.
  echo "NO-PROOF (degraded): $SMT"; exit 2
fi
if "$DRATTRIM" "$BASE.cnf" "$BASE.drat" > "$BASE.drat-output" 2>&1 && \
    grep -Eq '^[[:space:]]*s VERIFIED[[:space:]]*$' "$BASE.drat-output"; then
  # Honesty: a proof that assumed theory lemmas as axioms certifies the Boolean
  # skeleton only (lemmas justified in Phase C); report it distinctly so a
  # skeleton is never read as a full soundness certificate.
  assumed="$(sed -n 's/^c xolver-proof:.* \([0-9][0-9]*\) theory lemmas assumed.*/\1/p' "$BASE.cnf" | head -1)"
  if [ -z "$assumed" ]; then
    echo "VERIFIED-SKELETON (unknown theory provenance): $SMT"; exit 0
  elif [ "$assumed" -gt 0 ]; then
    echo "VERIFIED-SKELETON ($assumed lemmas assumed): $SMT"; exit 0
  fi
  echo "VERIFIED: $SMT"; exit 0
fi
echo "REJECTED (checker refused the proof — HARD FAILURE): $SMT"; exit 1
