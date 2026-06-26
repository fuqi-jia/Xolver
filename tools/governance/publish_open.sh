#!/usr/bin/env bash
#
# publish_open.sh — one-way export of the OPEN release from this monorepo.
#
# Model: the repo is open-by-default with a closed src/pro/ overlay. This produces
# a clean tree containing only files that (a) sit under a PUBLIC_ALLOWLIST top-level
# entry — default-private at the top level — and (b) are not under a private
# override (src/pro/). It then runs a leak gate. The export draws from
# `git ls-files`, so gitignored paths (docs/, CLAUDE.md, build/) never appear.
#
# For a real public release with clean history, run the same path filter through
# `git filter-repo --paths-from-file <allowlist> --invert-paths <private>`; this
# script demonstrates the strip + leak gate without rewriting history.
#
# Usage: tools/governance/publish_open.sh [out_dir]   (default: /tmp/xolver-open-export)
#
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"; cd "$ROOT"
OUT="${1:-/tmp/xolver-open-export}"
ALLOWLIST="$ROOT/PUBLIC_ALLOWLIST"

# Private overrides inside allowlisted trees (extended regex over repo-rel paths).
PRIVATE_RE='^src/pro/'

mapfile -t allow < <(grep -vE '^[[:space:]]*#|^[[:space:]]*$' "$ALLOWLIST")
is_allowed() {                       # $1 = repo-relative path
  local f="$1" top="${1%%/*}" a
  for a in "${allow[@]}"; do [ "$f" = "$a" ] || [ "$top" = "$a" ] && return 0; done
  return 1
}

rm -rf "$OUT"; mkdir -p "$OUT"
n=0; skipped_private=0; skipped_notallowed=0
while IFS= read -r f; do
  if [[ "$f" =~ $PRIVATE_RE ]]; then skipped_private=$((skipped_private+1)); continue; fi
  if ! is_allowed "$f"; then skipped_notallowed=$((skipped_notallowed+1)); continue; fi
  # Skip submodule gitlinks (dirs referenced via .gitmodules, not copied).
  [ -f "$f" ] || continue
  mkdir -p "$OUT/$(dirname "$f")"; cp "$f" "$OUT/$f"; n=$((n+1))
done < <(git ls-files)

# --- leak gate (must all pass before this export is ever published) ----------
fail=0
if find "$OUT/src/pro" -type f 2>/dev/null | grep -q .; then
  echo "LEAK: src/pro/ present in export"; fail=1; fi
if grep -rIl 'namespace xolver::pro\|DemoProEngine' "$OUT" 2>/dev/null | grep -q .; then
  echo "LEAK: pro symbols present in export"; fail=1; fi
# Open core must not include the pro tree (mirrors check_architecture.sh).
if grep -rIn '#include "pro/' "$OUT/src" 2>/dev/null | grep -q .; then
  echo "LEAK: open source includes pro/"; fail=1; fi
# The frozen SPI must be published (pro builds against it).
[ -f "$OUT/include/xolver/spi/SolverSpi.h" ] || { echo "MISSING: SPI header"; fail=1; }

{
  echo "=== publish_open ==="
  echo "exported:          $n files -> $OUT"
  echo "stripped private:  $skipped_private (src/pro/...)"
  echo "skipped !allowlist:$skipped_notallowed"
  echo "leak gate:         $([ $fail = 0 ] && echo PASS || echo FAIL)"
  echo "NOTE: also verify the export builds 0-unsound with pro absent — that is"
  echo "      just the default open build (XOLVER_BUILD_PRO=OFF)."
} >&2
exit $fail
