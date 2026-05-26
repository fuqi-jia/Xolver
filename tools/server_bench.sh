#!/bin/bash
# ============================================================================
# Zolver Distributed Benchmark — Server Deployment Script
#
# Run this ONCE from the compile host (Panda6, Ubuntu 22.04) after building.
# It distributes the binary and launches benchmarks across all 6 servers.
# ============================================================================

set -euo pipefail

# Configuration
SERVERS=("Panda1" "Panda2" "Panda3" "Panda4" "Panda5" "Panda6")
COMPILE_HOST="Panda6"
BUILD_DIR="${BUILD_DIR:-build}"
JOBS="${JOBS:-128}"
TIMEOUT="${TIMEOUT:-100}"
REMOTE_DIR="${REMOTE_DIR:-/data/zolver}"
LOCAL_BUILD="$(pwd)/${BUILD_DIR}"

# Logic assignment per server (adjust as needed)
declare -A LOGICS=(
    [Panda1]="lia,nia"
    [Panda2]="lra,nra"
    [Panda3]="lira,nira"
    [Panda4]="idl,rdl"
    [Panda5]="qf_uf,uflra"
    [Panda6]="uflia,ufnia,ufnra"
)

echo "=== Zolver Server Benchmark Deploy ==="
echo "Build dir: ${LOCAL_BUILD}"
echo "Servers: ${SERVERS[*]}"
echo "Jobs per server: ${JOBS}"
echo "Timeout: ${TIMEOUT}s"
echo ""

# Step 1: Verify binary exists
if [[ ! -f "${LOCAL_BUILD}/bin/zolver" ]]; then
    echo "ERROR: Binary not found at ${LOCAL_BUILD}/bin/zolver"
    echo "Run: mkdir build && cd build && cmake .. && cmake --build . -j\$(nproc)"
    exit 1
fi

# Step 2: Package
echo "[1/5] Packaging binary and scripts..."
TMPDIR=$(mktemp -d)
trap "rm -rf ${TMPDIR}" EXIT

mkdir -p "${TMPDIR}/zolver-dist/bin"
cp "${LOCAL_BUILD}/bin/zolver" "${TMPDIR}/zolver-dist/bin/"
chmod +x "${TMPDIR}/zolver-dist/bin/zolver"

mkdir -p "${TMPDIR}/zolver-dist/tools"
for f in run_benchmark.py analyze_benchmark.py bench_server.py freeze_baseline.py; do
    if [[ -f "tools/${f}" ]]; then
        cp "tools/${f}" "${TMPDIR}/zolver-dist/tools/"
    fi
done

PKG="${TMPDIR}/zolver-dist.tar.gz"
tar czf "${PKG}" -C "${TMPDIR}" zolver-dist
echo "Package: ${PKG} ($(du -h ${PKG} | cut -f1))"
echo ""

# Step 3: Distribute to all servers
echo "[2/5] Distributing to servers..."
for host in "${SERVERS[@]}"; do
    echo "  -> ${host}"
    ssh "${host}" "mkdir -p ${REMOTE_DIR} && sudo apt-get install -y libgmp10 libmpfr6 python3 >/dev/null 2>&1 || true" &
done
wait

for host in "${SERVERS[@]}"; do
    scp -q "${PKG}" "${host}:${REMOTE_DIR}/" &
done
wait

for host in "${SERVERS[@]}"; do
    ssh "${host}" "cd ${REMOTE_DIR} && tar xzf zolver-dist.tar.gz" &
done
wait
echo "Distribution complete."
echo ""

# Step 4: Launch benchmarks in parallel
echo "[3/5] Launching benchmarks (timeout=${TIMEOUT}s, jobs=${JOBS})..."
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RUN_DIR="${REMOTE_DIR}/run_${TIMESTAMP}"

for host in "${SERVERS[@]}"; do
    logic="${LOGICS[$host]}"
    echo "  ${host}: ${logic}"
    ssh -n "${host}" "
        cd ${REMOTE_DIR}/zolver-dist && \
        python3 tools/run_benchmark.py \
            --solver ./bin/zolver \
            --logic '${logic}' \
            -j ${JOBS} \
            -t ${TIMEOUT} \
            --dump-stats-dir ${RUN_DIR}/stats \
            --log-dir ${RUN_DIR}/logs \
            -o ${RUN_DIR} \
            > ${RUN_DIR}/bench.log 2>&1 && \
        echo '[DONE]' || echo '[FAILED]'
    " > /tmp/bench_${host}.log 2>&1 &
    echo "    PID=$! log=/tmp/bench_${host}.log"
done

echo ""
echo "All benchmarks launched in background."
echo "Monitor progress:"
echo "  for h in ${SERVERS[*]}; do echo \"\$h:\"; tail -1 /tmp/bench_\$h.log; done"
echo ""

# Step 5: Wait for completion
echo "[4/5] Waiting for all servers to finish..."
wait
echo "All benchmarks complete."
echo ""

# Step 6: Collect results
echo "[5/5] Collecting results to ${PWD}/server_results_${TIMESTAMP}/..."
mkdir -p "server_results_${TIMESTAMP}"
for host in "${SERVERS[@]}"; do
    scp -r "${host}:${RUN_DIR}/"* "server_results_${TIMESTAMP}/" 2>/dev/null || true
done

echo ""
echo "=== Done ==="
echo "Results: ${PWD}/server_results_${TIMESTAMP}/"
echo "Analyze: python3 tools/analyze_benchmark.py --current ${PWD}/server_results_${TIMESTAMP} --output analysis_${TIMESTAMP}"
