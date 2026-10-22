#!/bin/bash
# ============================================================================
# Xolver Static Build Script
#
# Produces a fully static xolver binary with zero dynamic dependencies.
# Can be uploaded to any Linux server regardless of glibc version.
#
# Usage:
#   ./tools/release/build_static.sh [build_dir]
#
# Output:
#   build_dir/bin/xolver   (statically linked, ~45MB)
# ============================================================================

set -euo pipefail

SRC_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
BUILD_DIR="${1:-${SRC_DIR}/build}"
if [[ "$BUILD_DIR" != /* ]]; then BUILD_DIR="${SRC_DIR}/${BUILD_DIR}"; fi
BUILD_DIR="$(realpath -m "$BUILD_DIR")"

echo "=== Xolver Static Build ==="
echo "Source:  ${SRC_DIR}"
echo "Build:   ${BUILD_DIR}"
echo ""

cd "${SRC_DIR}"

# Ensure submodules
if [[ ! -f "third_party/cadical/configure" ]]; then
    echo "[1/4] Initializing submodules..."
    git submodule update --init --recursive
fi

# Incrementally reconfigure the project's build directory. Never delete a path
# supplied by the caller, and serialize against other writers of this build.
mkdir -p "${BUILD_DIR}"
exec 9>"${BUILD_DIR}/.writer.lock"
flock 9

# Configure with static linking
echo "[2/4] Configuring (Release, static, CaseStats enabled)..."
cmake -S "${SRC_DIR}" -B "${BUILD_DIR}" \
    -DCMAKE_BUILD_TYPE=Release \
    -DXOLVER_STATIC_BUILD=ON \
    -DXOLVER_ENABLE_CASESTATS=ON \
    -DXOLVER_BUILD_TESTS=OFF \
    -DXOLVER_BUILD_TOOLS=ON

# Build
# WSL-safe: default to 2 jobs (unbounded -j$(nproc) has OOM-crashed WSL).
# Override on a beefy build server with BUILD_JOBS=$(nproc) or similar.
echo "[3/4] Building (-j${BUILD_JOBS:-2})..."
cmake --build "${BUILD_DIR}" --target xolver-cli -j"${BUILD_JOBS:-2}"

# Verify
echo "[4/4] Verifying static binary..."
BIN="${BUILD_DIR}/bin/xolver"
if [[ ! -f "${BIN}" ]]; then
    echo "ERROR: Binary not found at ${BIN}"
    exit 1
fi

echo ""
echo "Binary info:"
file "${BIN}"
echo ""
echo "Dynamic dependencies:"
ldd "${BIN}" 2>&1 || true
echo ""
echo "Size: $(du -h ${BIN} | cut -f1)"
echo ""
echo "Quick test:"
"${BIN}" solve "${SRC_DIR}/tests/regression/nia/nia_001_sat_x2_eq_4.smt2" 2>&1 | tail -1

echo ""
echo "=== Build complete ==="
echo "Binary: ${BIN}"
echo ""
echo "To package for servers:"
echo "  python3 tools/release/package_dist.py --build-dir ${BUILD_DIR} --output xolver-static.tar.gz"
