#!/usr/bin/env bash
#
# flag_census.sh — read-only census of XOLVER runtime feature flags.
#
# Phase 0 of the flag-refactor / open-core-SPI plan. Greps every flag read site
# (getenv("NAME"), env::paramInt/Long/Double("NAME", ...), env::flag("NAME", ...))
# and classifies each unique flag into one of four buckets:
#
#   A  diagnostic / profiling  — logging-only, zero effect on the result
#                                (names containing DIAG/PROF/TRACE, or ending
#                                 _DUMP/_STATS/_VERIFY/_LOG)
#   B  core tuning knob        — boolean/heuristic config that stays open-source
#   C  engine / feature select — enables a subsystem or picks an implementation;
#                                THIS bucket holds the open/closed (pro) boundary
#                                and is migrated by the SolverRegistry work, not
#                                as generic config. Each is flagged for the
#                                Phase-2 audit, with its construction site.
#   D  numeric-valued          — read through env::param* (budgets/caps/limits);
#                                these stay tunable per EnvParam.h.
#
# Output: a Markdown inventory (default docs/flags/INVENTORY.md) + a summary to
# stderr. Modeled on tools/governance/check_architecture.sh's find/grep idiom. Pure read;
# changes no behavior.
#
# Usage: tools/governance/flag_census.sh [output.md]
#
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

OUT="${1:-docs/flags/INVENTORY.md}"
mkdir -p "$(dirname "$OUT")"

SCAN_DIRS=(src include tools)

# --- 1. Extract (name, reader, file:line) for every flag read site ----------
# grep -rEno prints  path:line:matchedtext  ; matchedtext has no ':' and unix
# paths have no ':' , so the sed split on the first two ':' is safe.
extract() { # $1 = ERE, $2 = reader label
  grep -rEno "$1" "${SCAN_DIRS[@]}" --include='*.cpp' --include='*.h' 2>/dev/null \
    | sed -E "s|^([^:]+):([0-9]+):.*\"([A-Z0-9_]+)\".*|\3\t$2\t\1:\2|" || true
}

RAW="$(
  {
    extract '(std::)?getenv *\("[A-Z0-9_]+"'              getenv
    extract 'param(Int|Long|Double) *\("[A-Z0-9_]+"'      param
    extract '(env::)?flag *\("[A-Z0-9_]+"'                flag
    extract '(env::)?diag *\("[A-Z0-9_]+"'                diag
  }
)"

# Drop the few non-flag tokens (env reads that are not XOLVER feature flags but
# happen to match, e.g. PATH/HOME) by keeping only XOLVER_* plus the known
# unprefixed diagnostic families used in the codebase.
RAW="$(printf '%s\n' "$RAW" | grep -E '^(XOLVER_|ARITH_STAGE_|NIA_|BB_ASSERT_|EUF_|SOLVE_PHASE_)' || true)"

# --- 2. Aggregate + classify, emit one TSV row per unique flag --------------
ROWS="$(printf '%s\n' "$RAW" | awk -F'\t' '
  function isDiag(n) {
    return (n ~ /DIAG|PROF|TRACE|SELFPROF|HOTPROFILE/) || (n ~ /(_DUMP|_STATS|_VERIFY|_LOG)$/)
  }
  function isSelect(n) {
    return n ~ /MCSAT|CDCAC|EAGER_BITBLAST|NO_BITBLAST|LOCALSEARCH|FARKAS_OR|ZOHAR|PORTFOLIO|MODEL_BASED|RELEVANCY|_ENGINE|PLUGIN|NRA_CAC|SUBTROPICAL|LINEARIZE|PREELIM|NLEXT|SIGN_SPLIT|SIGN_REFUTE/
  }
  # Numeric-by-name: budgets/caps/limits read via raw getenv today (Phase 1
  # must route these through env::param). Suffix/segment families only.
  function isNumeric(n) {
    return n ~ /(_MS|_BUDGET|_BITS|_DEG|_PCT|_RATIO|_CAP|_MAX|_MIN|_LIMIT|_THRESHOLD|_LOOKAHEAD|_COUNT|_NODES|_DEPTH|_WIDTH|_EVERY|_MAXGROUP|_SAMPLE)$/ || n ~ /_MAX_|_BUDGET_|_LIMIT_/
  }
  {
    name=$1; reader=$2; site=$3
    count[name]++
    if (reader=="param") hasParam[name]=1
    if (reader=="getenv") hasGetenv[name]=1
    if (reader=="flag")  hasFlag[name]=1
    if (!(name in first)) first[name]=site
    f=site; sub(/:[0-9]+$/,"",f)
    if (index(SEP files[name] SEP, SEP f SEP)==0)
      files[name]=files[name] (files[name]?";":"") f
    if (f ~ /TheoryFactory|TheoryFactory\.cpp/)
      ctor[name]=ctor[name] (ctor[name]?", ":"") site
  }
  BEGIN { SEP="\x1f" }
  END {
    for (n in count) {
      nf=split(files[n], _a, ";")
      if (hasParam[n] || isNumeric(n)) cat="D"
      else if (isDiag(n)) cat="A"
      else if (isSelect(n)) cat="C"
      else cat="B"
      readers=""
      if (hasGetenv[n]) readers=readers (readers?"+":"") "getenv"
      if (hasParam[n])  readers=readers (readers?"+":"") "param"
      if (hasFlag[n])   readers=readers (readers?"+":"") "flag"
      printf "%s\t%s\t%d\t%d\t%s\t%s\t%s\n", cat, n, count[n], nf, readers, first[n], ctor[n]
    }
  }
' | sort -t$'\t' -k1,1 -k2,2)"

# --- 3. Counts per category --------------------------------------------------
total=$(printf '%s\n' "$ROWS" | grep -c . || true)
cA=$(printf '%s\n' "$ROWS" | awk -F'\t' '$1=="A"' | grep -c . || true)
cB=$(printf '%s\n' "$ROWS" | awk -F'\t' '$1=="B"' | grep -c . || true)
cC=$(printf '%s\n' "$ROWS" | awk -F'\t' '$1=="C"' | grep -c . || true)
cD=$(printf '%s\n' "$ROWS" | awk -F'\t' '$1=="D"' | grep -c . || true)
sites=$(printf '%s\n' "$RAW" | grep -c . || true)

# --- 4. Emit Markdown --------------------------------------------------------
{
  echo "# Flag inventory (Phase 0 census)"
  echo
  echo "> Generated by \`tools/governance/flag_census.sh\` (read-only). Auto-classification is a"
  echo "> first pass; **category C is a candidate list for the Phase-2 audit**, not a"
  echo "> verdict. Re-run after each migration phase to watch the buckets drain."
  echo
  echo "| Category | Meaning | Unique flags |"
  echo "|---|---|---|"
  echo "| A | diagnostic / profiling (logging-only) | ${cA} |"
  echo "| B | core tuning knob (stays open) | ${cB} |"
  echo "| C | engine/feature selector (**pro/open boundary**) | ${cC} |"
  echo "| D | numeric-valued (env::param, kept tunable) | ${cD} |"
  echo "| — | **total unique** / total read sites | **${total}** / ${sites} |"
  echo
  echo "## All flags"
  echo
  echo "| Cat | Flag | Reads | Files | Reader(s) | First site |"
  echo "|---|---|--:|--:|---|---|"
  printf '%s\n' "$ROWS" | awk -F'\t' 'NF>=6 {printf "| %s | %s | %d | %d | %s | %s |\n", $1,$2,$3,$4,$5,$6}'
  echo
  echo "## Category C — engine/feature selectors (Phase-2 audit candidates)"
  echo
  echo "Each must be classified \`{open-core | pro-candidate}\` in"
  echo "\`docs/spi/PRO-OPEN-BOUNDARY.md\`. Rows with a TheoryFactory construction site"
  echo "are the clearest registry seam candidates."
  echo
  echo "| Flag | Reads | Construction site(s) in TheoryFactory | First site |"
  echo "|---|--:|---|---|"
  printf '%s\n' "$ROWS" | awk -F'\t' '$1=="C" {printf "| %s | %d | %s | %s |\n", $2,$3,($7==""?"—":$7),$6}'
} > "$OUT"

# --- 5. Summary to stderr ----------------------------------------------------
{
  echo "=== flag census ==="
  echo "A (diag):   ${cA}"
  echo "B (knob):   ${cB}"
  echo "C (select): ${cC}   <- Phase-2 audit"
  echo "D (numeric):${cD}"
  echo "total unique: ${total}   read sites: ${sites}"
  echo "written: ${OUT}"
} >&2
