#!/usr/bin/env python3
"""Recheck frozen gate binaries with a short eager SAT time budget."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidate', required=True, type=Path)
    p.add_argument('--baseline', required=True, type=Path)
    p.add_argument('--inputs', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    records = []
    for key, binary in [('baseline', args.baseline), ('candidate', args.candidate)]:
        temp = args.output / (key + '-tmp')
        temp.mkdir()
        env = dict(os.environ, TMPDIR=str(temp), XOLVER_NIA_EAGER_BITBLAST_BUDGET_MS='50',
                   XOLVER_NIA_LINDECIDE_DIAG='1')
        command = [str(binary), '--test-case=NIA:*,NIA linear-decide:*,NIA-Core:*,*typed controls*,*array UF model*',
                   '--duration=true']
        start = time.monotonic()
        with (args.output / (key + '.log')).open('w') as out:
            try:
                result = subprocess.run(command, cwd=args.inputs, env=env, stdout=out,
                                        stderr=subprocess.STDOUT, timeout=90)
                rc = result.returncode
            except subprocess.TimeoutExpired:
                rc = 124
        records.append(dict(role=key, binary=str(binary), command=command, rc=rc,
                            sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                            seconds=time.monotonic() - start, eager_budget_ms=50, timeout=90))
    metrics = {r['role'] + '_unit_rc': r['rc'] for r in records}
    (args.output / 'report.json').write_text(json.dumps(dict(metrics=metrics, records=records), indent=2) + '\n')
    if os.environ.get('EOS_METRICS_FILE'):
        Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics) + '\n')
    print(json.dumps(metrics))
    return int(any(r['rc'] for r in records))


if __name__ == '__main__':
    raise SystemExit(main())
