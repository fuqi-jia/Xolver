#!/bin/bash
# EUF fix validation script — runs all affected logics sequentially
# Usage: nohup ./run_euf_validation.sh &
# Results: benchmark_results/<timestamp>/<logic>/

set -e

SOLVER="./build/bin/nlcolver"
JOBS=8
TIMEOUT=30
COMPARE="z3"

cd "$(dirname "$0")"

LOGICS=(
    QF_UF
    UFLIA
    UFLRA
    UFNIA
    UFNRA
    QF_LIA
    QF_LRA
)

for logic in "${LOGICS[@]}"; do
    echo "=========================================="
    echo "Running $logic ..."
    echo "=========================================="
    python tools/run_benchmark.py \
        --logic "$logic" \
        -j "$JOBS" \
        -t "$TIMEOUT" \
        --compare-with "$COMPARE"
    echo ""
done

echo "All done. Check benchmark_results/ for results."
