#!/bin/bash
# ============================================================================
# Zolver Static Build Script
#
# Produces a fully static zolver binary with zero dynamic dependencies.
# Can be uploaded to any Linux server regardless of glibc version.
#
# Usage:
#   ./tools/build_static.sh [build_dir]
#
# Output:
#   build_dir/bin/zolver   (statically linked, ~45MB)
# ============================================================================

set -euo pipefail

BUILD_DIR="${1:-build_static}"
SRC_DIR="$(cd "$(dirname "$0")/.." && pwd)"

echo "=== Zolver Static Build ==="
echo "Source:  ${SRC_DIR}"
echo "Build:   ${BUILD_DIR}"
echo ""

cd "${SRC_DIR}"

# Ensure submodules
if [[ ! -f "third_party/cadical/configure" ]]; then
    echo "[1/4] Initializing submodules..."
    git submodule update --init --recursive
fi

# Clean build
rm -rf "${BUILD_DIR}"
mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"

# Configure with static linking
echo "[2/4] Configuring (Release, static, CaseStats enabled)..."
cmake .. \
    -DCMAKE_BUILD_TYPE=Release \
    -DZOLVER_STATIC_BUILD=ON \
    -DZOLVER_ENABLE_CASESTATS=ON \
    -DZOLVER_BUILD_TESTS=OFF

# Build
echo "[3/4] Building..."
cmake --build . -j$(nproc)

# Verify
echo "[4/4] Verifying static binary..."
BIN="${SRC_DIR}/${BUILD_DIR}/bin/zolver"
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
echo "  python3 tools/package_dist.py --build-dir ${BUILD_DIR} --output zolver-static.tar.gz"
