#!/usr/bin/env bash
# Invoke through ExperimentOS. Reuse and serialize the single server build.
set -euo pipefail
cd "$(dirname "$0")/../.."
label="${1:?label required}"
overlay="${2:?source overlay required}"
baseline="${3:?frozen baseline solver required}"
[[ "$label" =~ ^[A-Za-z0-9_.-]+$ ]] || exit 2
baseline="$(realpath "$baseline")"
test -x "$baseline"
mkdir -p build validation
mkdir "validation/$label"
logdir="$PWD/validation/$label"
exec 9>build/.writer.lock
flock 9
# Capture the executing version before the overlay can replace its path.
cp "${BASH_SOURCE[0]}" "$logdir/driver.sh"
sha256sum "$logdir/driver.sh" > "$logdir/driver.sha256"
sha256sum "$overlay" > "$logdir/source-overlay.sha256"
python3 tools/remote/apply_overlay.py "$overlay" > "$logdir/overlay.log"
date -u +%FT%TZ > "$logdir/started"
hostname > "$logdir/host"
export LIBRARY_PATH="$PWD/dependencies/native/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_FLAGS='' \
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 -DBUILD_BOTH_LIBS=OFF \
    -DCMAKE_PREFIX_PATH="$PWD/dependencies/native" \
    -DGMP_LIBRARIES="$PWD/dependencies/native/lib/libgmp.a" \
    -DMPFR_LIBRARIES="$PWD/dependencies/native/lib/libmpfr.a" \
    -DXOLVER_ENABLE_PROOFS=ON -DXOLVER_BUILD_TESTS=ON -DXOLVER_BUILD_TOOLS=ON \
    -DFETCHCONTENT_SOURCE_DIR_DOCTEST="$PWD/dependencies/doctest" \
    -Dnlohmann_json_DIR="$PWD/dependencies/json/share/cmake/nlohmann_json" \
    > "$logdir/configure.log" 2>&1
cmake --build build --target xolver-cli xolver_unit_tests -j "${XOLVER_BUILD_JOBS:-4}" \
    > "$logdir/build.log" 2>&1
cp build/bin/xolver build/tests/xolver_unit_tests "$logdir/"
sha256sum "$logdir/xolver" "$logdir/xolver_unit_tests" "$baseline" > "$logdir/binaries.sha256"
python3 tools/remote/freeze_validation.py "$logdir/inputs" > "$logdir/input-freeze.log"
python3 tools/governance/control_catalog.py > "$logdir/catalog.log" 2>&1
python3 tools/governance/architecture.py --report "$logdir/architecture.json" > "$logdir/architecture.log" 2>&1
flock -u 9
export PYTHONDONTWRITEBYTECODE=1
mkdir "$logdir/tmp"
export TMPDIR="$logdir/tmp"
cd "$logdir/inputs"
set +e
XOLVER_NIA_EAGER_BITBLAST_BUDGET_MS=50 XOLVER_NIA_LINDECIDE_DIAG=1 timeout 90 "$logdir/xolver_unit_tests" \
    --test-case='NIA:*,NIA linear-decide:*,NIA-Core:*,*typed controls*,*array UF model*,NiaSolver*,GeneralSimplex:*,LraSolver:*,ModularResidue*,IntDivModLowerer*,PolynomialKernel*,LibPolyKernel*,RationalPolynomial*,PolynomialConverter*,BoundedNiaSolver*,NraLocalSearch*,NiaLocalSearch*,BitVec:*,Encoder:*,PolyBitBlaster:*,SpaceEstimator:*,BitBlastSolver*,Stress: randomized add/sub/mul*,Stress: randomized relZero*,Stress: randomized powConst*,Stress: mulConst*,Stress: boundary values*' --duration=true \
    > "$logdir/unit.log" 2>&1
unit_rc=$?
python3 tools/remote/check_gate.py --solver "$logdir/xolver" --baseline "$baseline" \
    --output "$logdir/paired" --timeout 6 --retry-timeout 20 \
    --z3 /pub/data/jiafq/xolver/dependencies/oracles/z3 \
    --cvc5 /pub/data/jiafq/z3-native-audit-tools-20260924-r3/cvc5/bin/cvc5 \
    > "$logdir/paired.log" 2>&1
paired_rc=$?
python3 tools/remote/freeze_validation.py "$logdir/inputs" --verify > "$logdir/input-integrity.log" 2>&1
integrity_rc=$?
set -e
date -u +%FT%TZ > "$logdir/finished"
python3 - "$logdir" "$unit_rc" "$paired_rc" "$integrity_rc" <<'PY'
import json, os, pathlib, sys
root = pathlib.Path(sys.argv[1])
metrics = dict(unit_rc=int(sys.argv[2]), paired_rc=int(sys.argv[3]), input_integrity_rc=int(sys.argv[4]))
report = root / 'paired/report.json'
if report.is_file():
    metrics.update(json.loads(report.read_text())['metrics'])
(root / 'metrics.json').write_text(json.dumps(metrics) + '\n')
if os.environ.get('EOS_METRICS_FILE'):
    pathlib.Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics) + '\n')
print(json.dumps(metrics))
PY
(( unit_rc == 0 && paired_rc == 0 && integrity_rc == 0 ))
