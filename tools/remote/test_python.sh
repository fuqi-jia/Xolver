#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")/../.."
label="${1:-python}"
[[ "$label" =~ ^[A-Za-z0-9_.-]+$ ]] || exit 2
out="validation/$label"
mkdir -p "$out"
PYTHONPATH="$PWD/build/python-package:$PWD/dependencies/python" \
    timeout 1200 /usr/bin/python3.12 -m pytest python/tests -q \
    --junitxml="$out/junit.xml" > "$out/pytest.log" 2>&1
rc=$?
python3 - "$rc" "$out" <<'PY'
import json, os, pathlib, sys
metrics = {'pytest_rc': int(sys.argv[1])}
(pathlib.Path(sys.argv[2]) / 'metrics.json').write_text(json.dumps(metrics)+'\n')
if os.environ.get('EOS_METRICS_FILE'):
    pathlib.Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics)+'\n')
PY
exit "$rc"
