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
verify_query() {
local BASE="$1" SMT="$2" verdict="$3"
expected="$(sed -n -E 's/;.*//; s/.*\(set-info[[:space:]]+:status[[:space:]]+(sat|unsat)\).*/\1/p' "$SMT" | tail -1)"
if { [ "$expected" = unsat ] && [ "$verdict" = sat ]; } || \
   { [ "$expected" = sat ] && [ "$verdict" = unsat ]; }; then
  echo "REJECTED (opposite verdict: expected=$expected actual=$verdict): $SMT"; return 1
fi

if [ "$verdict" != "unsat" ]; then
  echo "SKIP ($verdict): $SMT"; return 3
fi

# Prefer an Alethe theory proof when present. A rejected proof is a hard failure.
# The Alethe proof references post-normalization IR atoms, so it is checked
# against the IR-derived problem Xolver emits (<base>.smt2), not the original —
# the original->IR normalization is trusted preprocessing (Phase D obligation).
if [ -n "$CARCARA" ] && [ -s "$BASE.alethe" ] && [ -s "$BASE.smt2" ]; then
  if "$CARCARA" check "$BASE.alethe" "$BASE.smt2" > "$BASE.carcara-output" 2>&1 && \
      grep -Eq '^[[:space:]]*valid[[:space:]]*$' "$BASE.carcara-output"; then
    echo "VERIFIED (alethe/carcara): $SMT"; return 0
  fi
  echo "REJECTED (carcara refused the Alethe proof — HARD FAILURE): $SMT"; return 1
fi
if [ ! -s "$BASE.drat" ] || [ ! -s "$BASE.cnf" ]; then
  # Honest degraded mode: unsat decided outside the SAT core, no certificate.
  echo "NO-PROOF (degraded): $SMT"; return 2
fi
if "$DRATTRIM" "$BASE.cnf" "$BASE.drat" > "$BASE.drat-output" 2>&1 && \
    grep -Eq '^[[:space:]]*s VERIFIED[[:space:]]*$' "$BASE.drat-output"; then
  # Honesty: a proof that assumed theory lemmas as axioms certifies the Boolean
  # skeleton only (lemmas justified in Phase C); report it distinctly so a
  # skeleton is never read as a full soundness certificate.
  assumed="$(sed -n 's/^c xolver-proof:.* \([0-9][0-9]*\) theory lemmas assumed.*/\1/p' "$BASE.cnf" | head -1)"
  if [ -z "$assumed" ]; then
    echo "VERIFIED-SKELETON (unknown theory provenance): $SMT"; return 0
  elif [ "$assumed" -gt 0 ]; then
    echo "VERIFIED-SKELETON ($assumed lemmas assumed): $SMT"; return 0
  fi
  echo "VERIFIED: $SMT"; return 0
fi
echo "REJECTED (checker refused the proof — HARD FAILURE): $SMT"; return 1
}

mapfile -t verdicts < <(sed -n -E 's/^(sat|unsat|unknown)[[:space:]]*$/\1/p' "$BASE.stdout")
if [ "${#verdicts[@]}" -eq 0 ]; then
  echo "ERROR (no solver verdict): $SMT"; exit 4
fi
if [ -f "$BASE.queries" ]; then
  count="$(cat "$BASE.queries")"
  if [[ ! "$count" =~ ^[1-9][0-9]*$ ]] || [ "$count" != "${#verdicts[@]}" ]; then
    echo "ERROR (query/verdict count mismatch): $SMT"; exit 4
  fi
elif [ "${#verdicts[@]}" -ne 1 ]; then
  echo "ERROR (missing query manifest): $SMT"; exit 4
else
  verify_query "$BASE" "$SMT" "${verdicts[0]}"
  exit $?
fi

# Every query must be checked, including earlier UNSATs before a final SAT.
# Aggregate conservatively: any rejection/error fails the whole script;
# missing certificates remain degraded even if another query has a proof.
rejected=0 errors=0 no_proof=0 skipped=0
for ((i=1; i<=count; ++i)); do
  query_base="$BASE.query-$i"
  if [ ! -s "$query_base.input.smt2" ]; then
    echo "ERROR (missing query input $i): $SMT"; errors=1; continue
  fi
  if verify_query "$query_base" "$query_base.input.smt2" "${verdicts[i-1]}"; then rc=0; else rc=$?; fi
  case $rc in
    0) ;;
    1) rejected=1;;
    2) no_proof=1;;
    3) skipped=1;;
    *) errors=1;;
  esac
done
[ "$rejected" -eq 0 ] || exit 1
[ "$errors" -eq 0 ] || exit 4
[ "$no_proof" -eq 0 ] || exit 2
[ "$skipped" -eq 0 ] || exit 3
exit 0
