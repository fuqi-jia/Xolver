#!/usr/bin/env bash
# Shared server build; serialize all writers. Overlay extraction must use current
# timestamps: source edits may predate objects built for the original baseline.
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p build validation/candidate
exec 9>build/.writer.lock
flock 9
if [[ $# -gt 0 ]]; then
    python3 tools/remote/apply_overlay.py "$1"
fi
export LIBRARY_PATH="$PWD/dependencies/native/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
printf 'running\n' > validation/candidate/build.rc
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_FLAGS='' \
    -DXOLVER_ENABLE_PROOFS=ON -DXOLVER_BUILD_TESTS=ON -DXOLVER_BUILD_TOOLS=ON \
    -DBUILD_BOTH_LIBS=OFF -DCMAKE_PREFIX_PATH="$PWD/dependencies/native" \
    -DGMP_LIBRARIES="$PWD/dependencies/native/lib/libgmp.a" \
    -DMPFR_LIBRARIES="$PWD/dependencies/native/lib/libmpfr.a" \
    -DFETCHCONTENT_SOURCE_DIR_DOCTEST="$PWD/dependencies/doctest" \
    -Dnlohmann_json_DIR="$PWD/dependencies/json/share/cmake/nlohmann_json" \
    > validation/candidate/configure.log 2>&1
set +e
nice -n 10 cmake --build build --target xolver-cli xolver_unit_tests \
    -j "${XOLVER_BUILD_JOBS:-8}" > validation/candidate/build.log 2>&1
rc=$?
printf '%s\n' "$rc" > validation/candidate/build.rc
exit "$rc"
