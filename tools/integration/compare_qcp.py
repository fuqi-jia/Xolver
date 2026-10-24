#!/usr/bin/env python3
"""Replay one frozen QCP pure-condition corpus through independent solvers."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import subprocess
import time


def attempt(command, timeout):
    start = time.monotonic()
    record = {'command': command}
    try:
        ran = subprocess.run(command, text=True, capture_output=True, timeout=timeout)
        record.update(returncode=ran.returncode, stdout=ran.stdout, stderr=ran.stderr)
        words = ran.stdout.strip().splitlines()
        if ran.returncode:
            record['result'] = 'error'
        elif len(words) == 1 and words[0] in ('sat', 'unsat', 'unknown'):
            record['result'] = words[0]
        else:
            try:
                parsed = json.loads(ran.stdout)
                record['result'] = {'valid': 'unsat', 'invalid': 'sat', 'unknown': 'unknown'}[parsed['status']]
                record['details'] = parsed
            except (ValueError, KeyError, TypeError):
                record['result'] = 'error'
    except subprocess.TimeoutExpired:
        record['result'] = 'timeout'
    record['seconds'] = time.monotonic() - start
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--corpus', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--solver', required=True, type=Path)
    p.add_argument('--z3', required=True, type=Path)
    p.add_argument('--sv', type=Path)
    p.add_argument('--baseline', type=Path, help='frozen reference Xolver executable')
    p.add_argument('--timeout', type=float, default=10)
    args = p.parse_args()
    corpus = args.corpus.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((corpus / 'manifest.json').read_text())
    if not manifest['queries']:
        raise ValueError('a comparison requires at least one exported query')
    binaries = {name: path.resolve() for name, path in [('xolver', args.solver), ('z3', args.z3),
                ('sv', args.sv), ('baseline', args.baseline)] if path}
    report = {'binaries': {k: {'path': str(v), 'sha256': hashlib.sha256(v.read_bytes()).hexdigest()} for k, v in binaries.items()},
              'manifest_sha256': hashlib.sha256((corpus / 'manifest.json').read_bytes()).hexdigest(),
              'rows': [], 'disagreements': [], 'program_verified': False}
    counts = {name: collections.Counter() for name in binaries}
    for index, query in enumerate(manifest['queries']):
        path = (corpus / query['file']).resolve()
        if not path.is_relative_to(corpus) or hashlib.sha256(path.read_bytes()).hexdigest() != query['query_sha256']:
            raise ValueError('query integrity check failed: ' + str(path))
        row = {'query': query, 'attempts': {}}
        for name, binary in binaries.items():
            command = [str(binary), 'solve', str(path)] if name in ('xolver', 'baseline') else [str(binary), str(path)]
            record = attempt(command, args.timeout)
            row['attempts'][name] = record
            counts[name][record['result']] += 1
        definite = {a['result'] for a in row['attempts'].values()} & {'sat', 'unsat'}
        if len(definite) > 1:
            report['disagreements'].append(index)
        report['rows'].append(row)
        if index % 50 == 0:
            print(index, {k: dict(v) for k, v in counts.items()}, flush=True)
    report['counts'] = {k: dict(v) for k, v in counts.items()}
    report['shared_decisions'] = sum(all(a['result'] in ('sat', 'unsat') for a in r['attempts'].values()) for r in report['rows'])
    report['interval_certificates'] = sum(r['attempts'].get('sv', {}).get('details', {}).get('method') == 'interval' for r in report['rows'])
    report['matched_z3_decisions'] = {name: sum(
        r['attempts'][name]['result'] in ('sat', 'unsat') and
        r['attempts'][name]['result'] == r['attempts']['z3']['result'] for r in report['rows'])
        for name in binaries}
    report['process_wall_seconds'] = {name: sum(r['attempts'][name]['seconds'] for r in report['rows']) for name in binaries}
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('counts', 'shared_decisions', 'interval_certificates', 'disagreements')}))
    # Unknowns are measured, never counted as agreements or as proved programs.
    return 1 if report['disagreements'] or any(v['error'] for v in counts.values()) else 0


if __name__ == '__main__':
    raise SystemExit(main())
