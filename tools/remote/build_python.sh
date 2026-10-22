#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
label="${1:-python}"
[[ "$label" =~ ^[A-Za-z0-9_.-]+$ ]] || exit 2
out="validation/$label"
mkdir -p build "$out"
exec 9>build/.writer.lock
flock 9
export LIBRARY_PATH="$PWD/dependencies/native/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
cmake -S . -B build -DXOLVER_BUILD_PYTHON=ON -DPYBIND11_FINDPYTHON=ON \
    -DPython_EXECUTABLE=/usr/bin/python3.12 -DPython3_EXECUTABLE=/usr/bin/python3.12 \
    -Dpybind11_DIR="$PWD/dependencies/python/pybind11/share/cmake/pybind11" \
    -DGMP_LIBRARIES=/usr/lib/x86_64-linux-gnu/libgmp.so.10 \
    -DMPFR_LIBRARIES=/usr/lib/x86_64-linux-gnu/libmpfr.so.6 \
    > "$out/configure.log" 2>&1
nice -n 10 cmake --build build --target _xolver -j "${XOLVER_BUILD_JOBS:-8}" \
    > "$out/build.log" 2>&1
/usr/bin/python3.12 - <<'PY'
from pathlib import Path
import shutil
package = Path('build/python-package/xolver')
shutil.copytree('python/xolver', package, dirs_exist_ok=True)
modules = list(Path('build/python').glob('_xolver*.so'))
if len(modules) != 1:
    raise SystemExit('expected exactly one built Python extension')
shutil.copy2(modules[0], package / modules[0].name)
PY
sha256sum build/python-package/xolver/_xolver*.so > "$out/binary.sha256"
printf '0\n' > "$out/build.rc"
