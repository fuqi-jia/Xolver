#!/usr/bin/env bash
set -euo pipefail

fail=0

check_forbidden() {
  local pattern="$1"
  local path="$2"
  local msg="$3"

  local matches
  matches=$(find "$path" -type f \( -name '*.h' -o -name '*.cpp' \) -exec grep -l "$pattern" {} + 2>/dev/null || true)
  if [ -n "$matches" ]; then
    echo "ARCH VIOLATION: $msg"
    echo "$matches" | head -5
    fail=1
  fi
}

echo "=== Checking architecture constraints ==="

# sat/ -> theory/ with whitelist for thin callback interfaces
sat_theory_lines=$(find src/sat -type f \( -name '*.h' -o -name '*.cpp' \) -exec grep -Hn '#include "theory/' {} + 2>/dev/null | grep -v 'TheoryPropagatorCallbacks.h' | grep -v 'TheoryAssignmentView.h' || true)
if [ -n "$sat_theory_lines" ]; then
  echo "ARCH VIOLATION: sat/ must not include theory/ (whitelisted: TheoryPropagatorCallbacks.h, TheoryAssignmentView.h)"
  echo "$sat_theory_lines" | cut -d: -f1 | sort -u | head -5
  fail=1
fi

check_forbidden '#include "frontend/' src/sat \
  "sat/ must not include frontend/"

check_forbidden '#include "sat/' src/expr \
  "expr/ must not include sat/"

check_forbidden '#include "theory/' src/expr \
  "expr/ must not include theory/"

check_forbidden '#include "frontend/' src/expr \
  "expr/ must not include frontend/"

check_forbidden '#include "theory/euf/' src/theory/core \
  "theory/core must not depend on euf/"

# api/Solver.cpp must not directly reference concrete solvers (ignore comments)
api_solver_refs=$(grep -n 'LraSolver\|LiaSolver\|NraSolver\|NiaSolver\|EufSolver' src/api/Solver.cpp 2>/dev/null | grep -v '^[0-9]*:\s*//' || true)
if [ -n "$api_solver_refs" ]; then
  echo "ARCH VIOLATION: api/Solver.cpp must not directly reference concrete solvers"
  echo "$api_solver_refs" | head -5
  fail=1
fi

# Phase 3: engine-selector flags migrated to the typed env::flag reader must not
# be read via raw getenv anywhere in src (so they register in the
# XOLVER_DUMP_PARAMS autotuner surface and selection stays centralized). Only
# flags whose EVERY read is env::flag are listed — XOLVER_NIA_NO_BITBLAST is
# intentionally excluded (it has presence-semantics readers that env::flag,
# which is not-zero semantics, cannot replace).
for _f in XOLVER_NRA_MCSAT XOLVER_NIA_MCSAT XOLVER_NIA_CDCAC XOLVER_NIA_LOCALSEARCH; do
  check_forbidden "getenv(\"$_f\")" src \
    "$_f is a migrated engine-selector (Phase 3) — read via env::flag, not raw getenv"
done

# SPI boundary (Phase 4): the public SPI headers must stay narrow — no concrete
# solver/engine internals — so a closed pro module stays decoupled from the open
# core. (expr/ IR foundation is allowed; theory/ and sat/ are not.)
check_forbidden '#include "theory/' include/xolver/spi \
  "SPI headers (include/xolver/spi) must not include theory/ internals"

check_forbidden '#include "sat/' include/xolver/spi \
  "SPI headers (include/xolver/spi) must not include sat/ internals"

# Open core must never depend on the closed pro tree, so the open build is whole
# with src/pro/ absent. (src/pro/ may include itself; every other subtree is open.)
for _d in src/expr src/sat src/theory src/frontend src/api src/util src/proof src/parser; do
  check_forbidden '#include "pro/' "$_d" \
    "open core ($_d) must not include src/pro/"
done

if [ "$fail" -eq 0 ]; then
  echo "=== All architecture constraints satisfied ==="
else
  echo "=== Architecture violations found ==="
fi

exit "$fail"
