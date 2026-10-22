#!/usr/bin/env bash
# Run through ExperimentOS on the server. One incremental build per checkout.
set -euo pipefail
cd "$(dirname "$0")/../.."
label="${1:?validation label required}"
[[ "$label" =~ ^[A-Za-z0-9_.-]+$ ]] || exit 2
mkdir -p build validation
mkdir "validation/$label"
exec 9>build/.writer.lock
flock 9
logdir="$PWD/validation/$label"
if [[ $# -gt 1 ]]; then
    sha256sum "$2" > "$logdir/source-overlay.sha256"
    python3 tools/remote/apply_overlay.py "$2" > "$logdir/overlay.log"
fi
date -u +%FT%TZ > "$logdir/started"
hostname > "$logdir/host"
export LIBRARY_PATH="$PWD/dependencies/native/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_CXX_FLAGS='' \
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
    -DBUILD_BOTH_LIBS=OFF \
    -DCMAKE_PREFIX_PATH="$PWD/dependencies/native" \
    -DGMP_LIBRARIES="$PWD/dependencies/native/lib/libgmp.a" \
    -DMPFR_LIBRARIES="$PWD/dependencies/native/lib/libmpfr.a" \
    -DXOLVER_ENABLE_PROOFS=ON \
    -DXOLVER_BUILD_TESTS=ON -DXOLVER_BUILD_TOOLS=ON \
    -DFETCHCONTENT_SOURCE_DIR_DOCTEST="$PWD/dependencies/doctest" \
    -Dnlohmann_json_DIR="$PWD/dependencies/json/share/cmake/nlohmann_json" \
    > "$logdir/configure.log" 2>&1
cmake --build build --target xolver-cli xolver_unit_tests xolver_checker_tests xolver_sl_cases -j "${XOLVER_BUILD_JOBS:-4}" > "$logdir/build.log" 2>&1
cp build/bin/xolver "$logdir/xolver"
cp build/tests/xolver_unit_tests "$logdir/xolver_unit_tests"
cp build/tests/xolver_checker_tests "$logdir/xolver_checker_tests"
cp build/tests/xolver_sl_cases "$logdir/xolver_sl_cases"
sha256sum "$logdir/xolver" "$logdir/xolver_unit_tests" "$logdir/xolver_checker_tests" "$logdir/xolver_sl_cases" > "$logdir/binaries.sha256"
cp build/tests/CMakeFiles/xolver_checker_tests.dir/link.txt "$logdir/checker-link.txt"
inputs="$logdir/inputs"
python3 tools/remote/freeze_validation.py "$inputs" > "$logdir/input-freeze.log"
# Architecture inspects the live source tree and must run before releasing the
# writer lock. All subsequent Python/SMT inputs are immutable run artifacts.
set +e
python3 tools/governance/architecture.py --report "$logdir/architecture.json" > "$logdir/architecture.log" 2>&1
architecture_rc=$?
set -e
# Freeze binaries and small test sources, never another build tree. Later
# overlays/builds cannot change the inputs of this already-running validation.
flock -u 9
export PYTHONDONTWRITEBYTECODE=1
mkdir "$logdir/tmp"
# Several API tests use fixed temporary basenames. Isolate concurrent runs and
# make directory-scanning C++ tests consume the same frozen inputs as Python.
export TMPDIR="$logdir/tmp"
run_frozen() (
    cd "$inputs"
    "$@"
)
run_frozen timeout 120 "$logdir/xolver_unit_tests" \
    --test-case='*native*,*PA reconstructs*,*defined-variable*,*typed controls*,*polynomial literal*,*SL Boolean heap*' \
    > "$logdir/unit-preflight.log" 2>&1
set +e
run_frozen "$logdir/xolver_checker_tests" > "$logdir/checker.log" 2>&1
checker_rc=$?
run_frozen timeout 1200 "$logdir/xolver_unit_tests" --duration=true > "$logdir/unit.log" 2>&1
unit_rc=$?
python3 "$inputs/tools/regression/run_regression.py" --solver "$logdir/xolver" \
    --root "$inputs/tests/regression" \
    --timeout "${XOLVER_REGRESSION_TIMEOUT:-60}" -j "${XOLVER_REGRESSION_JOBS:-4}" \
    --report "$logdir/regression.json" > "$logdir/regression.log" 2>&1
regression_rc=$?
XOLVER_TEST_SOLVER="$logdir/xolver" python3 -m unittest discover \
    -s "$inputs/tests/tools" -p 'test_*.py' > "$logdir/tools.log" 2>&1
tools_rc=$?
python3 "$inputs/tools/regression/run_regression.py" --root "$inputs/tests/known_gaps" \
    --solver "$logdir/xolver" --allow-unknown --timeout 20 -j 2 \
    --report "$logdir/known-gaps.json" \
    > "$logdir/known-gaps.log" 2>&1
gaps_rc=$?
python3 "$inputs/tools/remote/freeze_validation.py" "$inputs" --verify > "$logdir/input-integrity.log" 2>&1
input_integrity_rc=$?
set -e
date -u +%FT%TZ > "$logdir/finished"
python3 - "$logdir" "$unit_rc" "$regression_rc" "$tools_rc" "$gaps_rc" "$checker_rc" "$architecture_rc" "$input_integrity_rc" <<'PY'
import json, os, pathlib, sys
root = pathlib.Path(sys.argv[1])
metrics = {"unit_rc": int(sys.argv[2]), "regression_rc": int(sys.argv[3]),
           "tools_rc": int(sys.argv[4]), "known_gaps_rc": int(sys.argv[5]),
           "checker_rc": int(sys.argv[6]), "architecture_rc": int(sys.argv[7]),
           "input_integrity_rc": int(sys.argv[8])}
(root / "metrics.json").write_text(json.dumps(metrics) + "\n")
if os.environ.get("EOS_METRICS_FILE"):
    pathlib.Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
PY
(( unit_rc == 0 && regression_rc == 0 && tools_rc == 0 && gaps_rc == 0 && checker_rc == 0 && architecture_rc == 0 && input_integrity_rc == 0 ))
