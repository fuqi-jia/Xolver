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

if [ "$fail" -eq 0 ]; then
  echo "=== All architecture constraints satisfied ==="
else
  echo "=== Architecture violations found ==="
fi

exit "$fail"
