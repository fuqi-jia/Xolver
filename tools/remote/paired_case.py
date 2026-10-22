#!/usr/bin/env python3
"""One full-core EOS run per input/version; report timeouts separately."""
import argparse
from dataclasses import asdict
import json
import os
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'regression'))
from run_regression import run_case

p = argparse.ArgumentParser()
p.add_argument('--version', choices=['baseline', 'candidate'], required=True)
p.add_argument('--case', required=True)
p.add_argument('--timeout', type=float, default=240)
a = p.parse_args()
root = Path(__file__).resolve().parents[2]
paths = list((root / 'tests/regression').rglob(a.case))
if len(paths) != 1:
    raise SystemExit('case must resolve to one unique regression input')
r = run_case(str(paths[0]), str(root / 'validation' / a.version / 'xolver'), a.timeout, 'pass')
result = asdict(r)
result['path'] = str(r.path.relative_to(root))
result['version'] = a.version
result['solved'] = int(r.verdict == 'PASS')
result['soundness_failure'] = int(r.verdict == 'UNSOUND')
result['execution_error'] = int(r.verdict == 'ERROR')
out = root / 'validation/paired' / a.version / (a.case + '.json')
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(result, indent=2) + '\n')
if os.environ.get('EOS_METRICS_FILE'):
    Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(result) + '\n')
print(json.dumps(result))
raise SystemExit(int(r.verdict not in {'PASS', 'TIMEOUT'}))
