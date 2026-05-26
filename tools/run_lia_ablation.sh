#!/bin/bash
# ============================================================================
# Run LIA mismatch replay across all ablation modes.
#
# Usage:
#   ./tools/run_lia_ablation.sh \
#       --discrepancies panda-results/2026-05-21/lia/discrepancies.txt \
#       --category convert \
#       --zolver ./build/bin/zolver \
#       --output-base ./lia_ablation_results
#
# Output structure:
#   lia_ablation_results/
#     normal/          (baseline, always included)
#     safe/
#     ultra-safe/
#     safe+single-var/
#     safe+gcd-ineq/
#     safe+eq-gcd/
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Defaults
DISCREPANCIES=""
CATEGORY=""
ZOLVER="./build/bin/zolver"
Z3="z3"
LIMIT=""
TIMEOUT=""
OUTPUT_BASE="./lia_ablation_results"

# Parse args
while [[ $# -gt 0 ]]; do
    case "$1" in
        --discrepancies) DISCREPANCIES="$2"; shift 2 ;;
        --category) CATEGORY="$2"; shift 2 ;;
        --zolver) ZOLVER="$2"; shift 2 ;;
        --z3) Z3="$2"; shift 2 ;;
        --limit) LIMIT="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        --output-base) OUTPUT_BASE="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

if [[ -z "$DISCREPANCIES" ]]; then
    echo "ERROR: --discrepancies is required"
    exit 1
fi

mkdir -p "$OUTPUT_BASE"

# Mode definitions: "dir_name:extra_flags"
MODES=(
    "safe:--lia-safe-mode"
    "ultra-safe:--lia-ultra-safe-mode"
    "safe+single-var:--lia-safe-mode --lia-enable-single-var-tightening"
    "safe+gcd-ineq:--lia-safe-mode --lia-enable-gcd-ineq-tightening"
    "safe+eq-gcd:--lia-safe-mode --lia-enable-eq-gcd-normalization"
)

for entry in "${MODES[@]}"; do
    dir_name="${entry%%:*}"
    extra_flags="${entry#*:}"
    outdir="$OUTPUT_BASE/$dir_name"
    mkdir -p "$outdir"

    echo ""
    echo "========================================"
    echo "Running mode: $dir_name"
    echo "Extra flags:  $extra_flags"
    echo "Output dir:   $outdir"
    echo "========================================"

    cmd=(
        python3 "$SCRIPT_DIR/lia_mismatch_replay.py"
        --discrepancies "$DISCREPANCIES"
        --zolver "$ZOLVER"
        --z3 "$Z3"
        --mode-name "$dir_name"
        --zolver-extra="$extra_flags"
        --out "$outdir/report.json"
    )

    if [[ -n "$CATEGORY" ]]; then
        cmd+=(--category "$CATEGORY")
    fi
    if [[ -n "$LIMIT" ]]; then
        cmd+=(--limit "$LIMIT")
    fi
    if [[ -n "$TIMEOUT" ]]; then
        cmd+=(--timeout "$TIMEOUT")
    fi

    "${cmd[@]}" 2>&1 | tee "$outdir/run.log"
done

echo ""
echo "========================================"
echo "All modes complete. Results in: $OUTPUT_BASE"
echo "========================================"

# Quick summary
for entry in "${MODES[@]}"; do
    dir_name="${entry%%:*}"
    report="$OUTPUT_BASE/$dir_name/report.json"
    if [[ -f "$report" ]]; then
        fixed=$(python3 -c "import json,sys; d=json.load(open('$report')); print(d['summary']['fixed'])" 2>/dev/null || echo "?")
        total=$(python3 -c "import json,sys; d=json.load(open('$report')); print(d['summary']['total'])" 2>/dev/null || echo "?")
        still=$(python3 -c "import json,sys; d=json.load(open('$report')); print(d['summary']['still_mismatch'])" 2>/dev/null || echo "?")
        printf "  %-20s fixed=%s/%s  still_mismatch=%s\n" "$dir_name" "$fixed" "$total" "$still"
    fi
done
