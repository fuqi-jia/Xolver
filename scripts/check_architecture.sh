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

check_forbidden '#include "theory/' src/sat \
  "sat/ must not include theory/"

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

check_forbidden 'LraSolver\|LiaSolver\|NraSolver\|NiaSolver\|EufSolver' src/api/Solver.cpp \
  "api/Solver.cpp must not directly reference concrete solvers"

if [ "$fail" -eq 0 ]; then
  echo "=== All architecture constraints satisfied ==="
else
  echo "=== Architecture violations found ==="
fi

exit "$fail"
