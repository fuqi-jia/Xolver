#!/usr/bin/env bash
# Adversarial soundness self-test for the Boolean-core proof checker.
#
# A proof checker is only a soundness gate if it REJECTS invalid proofs. This
# script proves that — empirically, on tiny crafted instances — for the checker
# we depend on. It must be run before trusting any checker as the unsat gate, and
# it runs in the Phase-E proof CI lane as a meta-check on the gate itself.
#
# Findings (Phase A, 2026-06-26), recorded so the choice is reproducible:
#   * drat-trim (full forward RUP) is ADVERSARIALLY SOUND: it rejects a bogus
#     empty-clause "proof" of a SATISFIABLE formula ("conflict claimed, but not
#     detected", exit 1) and verifies a valid one (exit 0). -> use as the gate.
#   * lrat-check (shipped in the drat-trim repo) trusts solver-supplied hints and
#     rubber-stamps an empty clause when the listed hints do not independently
#     conflict. Fine for genuine solver output; NOT a gate against a wrong proof.
#     -> never the sole gate; cake_lpr (CakeML-verified) is the hardened floor.
#
# Usage: checker-soundness-test.sh <path-to-drat-trim>
set -euo pipefail
DT="${1:?usage: checker-soundness-test.sh <drat-trim binary>}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"

fail() { echo "SOUNDNESS-SELF-TEST FAILED: $1" >&2; exit 1; }

# UNSAT formula (x) ^ (-x); valid DRAT derives the empty clause.
printf 'p cnf 1 2\n1 0\n-1 0\n' > unsat.cnf
printf '0\n'                     > valid.drat
# SAT formula (x) ^ (y); bogus DRAT claims the empty clause (NOT entailed).
printf 'p cnf 2 2\n1 0\n2 0\n'   > sat.cnf
printf '0\n'                     > bogus.drat

# 1) The checker MUST verify a valid UNSAT proof.
if ! "$DT" unsat.cnf valid.drat >/dev/null 2>&1; then
  fail "drat-trim rejected a VALID unsat proof (false negative)"
fi
echo "ok: valid unsat proof verified"

# 2) The checker MUST reject a bogus proof of a SAT formula. A checker that
#    accepts this cannot catch a wrong proof and is unfit as a soundness gate.
if "$DT" sat.cnf bogus.drat >/dev/null 2>&1; then
  fail "drat-trim ACCEPTED a bogus proof of a SAT formula (UNSOUND checker!)"
fi
echo "ok: bogus proof of SAT formula rejected"

echo "CHECKER SOUNDNESS SELF-TEST PASSED ($DT is adversarially sound)"
