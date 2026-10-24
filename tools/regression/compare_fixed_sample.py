#!/usr/bin/env python3
"""Balanced, reproducible comparisons on pre-frozen SMT-LIB case manifests."""
import argparse
import collections
import hashlib
import json
import math
import os
from pathlib import Path
import random
import statistics
import subprocess
import time


def invoke(command, timeout):
    started = time.monotonic()
    row = {'command': command}
    try:
        ran = subprocess.run(command, text=True, capture_output=True, timeout=timeout)
        answers = [s.strip() for s in ran.stdout.splitlines() if s.strip() in ('sat', 'unsat', 'unknown')]
        row.update(returncode=ran.returncode, stdout=ran.stdout[:4096], stderr=ran.stderr[:4096])
        row['result'] = answers[0] if ran.returncode == 0 and len(answers) == 1 else 'error'
    except subprocess.TimeoutExpired:
        row['result'] = 'timeout'
    row['seconds'] = time.monotonic() - started
    return row


def summarize(rows, timeout):
    names = ['baseline', 'candidate', 'z3']
    counts = {n: collections.Counter() for n in names}
    solved = {n: 0 for n in names}
    wrong = []
    par2 = {n: 0.0 for n in names}
    common = []
    for i, row in enumerate(rows):
        observations = row['observations']
        for pair in observations:
            oracle = pair['z3']['result']
            for n in names:
                result = pair[n]['result']
                counts[n][result] += 1
                par2[n] += pair[n]['seconds'] if result in ('sat', 'unsat') else 2 * timeout
                expected = row['case'].get('expected', 'unknown')
                if result in ('sat', 'unsat') and (
                    oracle in ('sat', 'unsat') and result != oracle or
                    expected in ('sat', 'unsat') and result != expected):
                    wrong.append(dict(index=i, solver=n, result=result, oracle=oracle, expected=expected))
        for n in names:
            answers = {pair[n]['result'] for pair in observations}
            solved[n] += len(answers) == 1 and next(iter(answers)) in ('sat', 'unsat')
        answers = {pair[n]['result'] for pair in observations for n in names}
        if len(answers) == 1 and next(iter(answers)) in ('sat', 'unsat'):
            times = {n: statistics.median(pair[n]['seconds'] for pair in observations) for n in names}
            common.append((row['case'].get('family', '_'), times))
    speedups = {}
    for reference in ['baseline', 'z3']:
        families = collections.defaultdict(list)
        for family, times in common:
            families[family].append(math.log(times[reference] / times['candidate']))
        values = [statistics.mean(v) for v in families.values()]
        if values:
            rng = random.Random(20261025)
            boot = sorted(math.exp(statistics.mean(rng.choices(values, k=len(values)))) for _ in range(2000))
            speedups[reference] = dict(family_geomean=math.exp(statistics.mean(values)),
                                      family_bootstrap_95=[boot[50], boot[1949]], families=len(values))
    return dict(inputs=len(rows), counts={n: dict(c) for n, c in counts.items()},
                consistently_decided=solved, par2_process_seconds=par2, wrong_verdicts=wrong,
                common_decided=len(common), candidate_speedup=speedups,
                latency_scope='medians on cases all solvers decide consistently; equal family weights; fresh processes')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--candidate', type=Path, required=True)
    p.add_argument('--z3', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--timeout', type=float, default=3)
    args = p.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if not manifest['cases']:
        raise ValueError('no cases')
    args.output.mkdir(parents=True, exist_ok=False)
    binaries = {n: getattr(args, n).resolve() for n in ['baseline', 'candidate', 'z3']}
    report = {'manifest_sha256': hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
              'binaries': {n: dict(path=str(b), sha256=hashlib.sha256(b.read_bytes()).hexdigest()) for n, b in binaries.items()},
              'timeout': args.timeout, 'affinity': sorted(os.sched_getaffinity(0)), 'rows': []}
    for index, case in enumerate(manifest['cases']):
        path = Path(case['path'])
        if hashlib.sha256(path.read_bytes()).hexdigest() != case['sha256']:
            raise ValueError('case hash mismatch: ' + str(path))
        row = {'case': case, 'observations': []}
        for repetition in range(case.get('repetitions', 1)):
            names = list(binaries)
            start = (index + repetition) % len(names)
            names = names[start:] + names[:start]
            pair = {}
            for n in names:
                command = [str(binaries[n]), str(path)] if n == 'z3' else [str(binaries[n]), 'solve', str(path)]
                pair[n] = invoke(command, args.timeout)
            row['observations'].append(pair)
        report['rows'].append(row)
        (args.output / 'progress.json').write_text(json.dumps(dict(completed=index+1,total=len(manifest['cases'])))+'\n')
    report['summary'] = summarize(report['rows'], args.timeout)
    report['per_logic'] = {logic: summarize([r for r in report['rows'] if r['case'].get('logic') == logic], args.timeout)
                           for logic in sorted({r['case'].get('logic', 'unspecified') for r in report['rows']})}
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['summary']))
    return int(bool(report['summary']['wrong_verdicts']) or any(
        c.get('error', 0) for c in report['summary']['counts'].values()))


if __name__ == '__main__':
    raise SystemExit(main())
