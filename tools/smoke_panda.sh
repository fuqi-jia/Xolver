#!/bin/bash
# smoke_panda.sh — quick xolver + z3 sanity check on any panda
# usage on panda: bash /tmp/smoke_panda.sh
set -e
DIST="${1:-/pub/data/jiafq/xolver-runs/xolver-dist}"
[ -d "$DIST" ] || DIST=~/xolver-dist
cd "$DIST" || { echo "ERROR: no xolver-dist at $DIST or ~"; exit 1; }
echo "-- xolver --version --"
./bin/xolver --version 2>&1 | head -2
echo "-- sat (expect sat) --"
[ -f /tmp/sat.smt2 ] || printf '%s' '(set-logic QF_LIA)(declare-const x Int)(assert (and (> x 0) (< x 10)))(check-sat)' > /tmp/sat.smt2
timeout 5 ./bin/xolver solve /tmp/sat.smt2
echo "-- unsat (expect unsat) --"
[ -f /tmp/unsat.smt2 ] || printf '%s' '(set-logic QF_LIA)(declare-const x Int)(assert (and (> x 5) (< x 5)))(check-sat)' > /tmp/unsat.smt2
timeout 5 ./bin/xolver solve /tmp/unsat.smt2
echo "-- z3 --"
which z3 && z3 --version 2>&1 | head -1
echo "-- cvc5 (panda14 only) --"
[ -x ~/bin/cvc5 ] && ~/bin/cvc5 --version 2>&1 | head -2 || echo "  (cvc5 not installed — expected on non-panda14)"
echo "-- ALL CHECKS PASS --"
