#!/usr/bin/env python3
"""Summarize a frozen, hash-consistent comparison with explicit truth evidence."""
import argparse
from collections import Counter
import json
from pathlib import Path


def summarize(directory, expected_cases):
    reports = [json.loads(p.read_text()) for p in sorted(directory.glob('case-*/report.json'))]
    if len(reports) != expected_cases:
        raise ValueError(f'expected {expected_cases} complete reports, got {len(reports)}')
    if len({r['index'] for r in reports}) != expected_cases:
        raise ValueError('duplicate input indices')
    if len({r['case']['sha256'] for r in reports}) != expected_cases:
        raise ValueError('duplicate input hashes')
    first = reports[0]
    for row in reports:
        for key in ('binaries', 'manifest_sha256', 'timeout', 'memory_bytes'):
            if row[key] != first[key]:
                raise ValueError('mixed protocol or frozen versions: ' + key)
        if len({o['cpu'] for o in row['observations'].values()}) != 1:
            raise ValueError('versions did not share one CPU: ' + str(row['index']))
        if row.get('protocol_errors'):
            raise ValueError('wall budget overrun: ' + str(row['index']))
        for observation in row['observations'].values():
            for attempt in [observation, *(observation[key] for key in
                    ('model', 'replay', 'unsat_check') if key in observation)]:
                if attempt.get('budget_overrun') or attempt.get('seconds', 0) > row['timeout'] + 1:
                    raise ValueError('wall budget overrun: ' + str(row['index']))
    counts = {name: Counter() for name in first['binaries']}
    wrong, invalid_models, unverified, comparisons = [], [], [], []
    by_logic = {}
    for row in reports:
        observations = row['observations']
        decisive = {o['result'] for o in observations.values() if o['result'] in ('sat', 'unsat')}
        contradiction = row['wrong_verdict'] or len(decisive) > 1
        if contradiction:
            wrong.append(row['index'])
        sat_evidence, unsat_evidence = [], []
        for name, observation in observations.items():
            if observation.get('replay', {}).get('result') == 'sat':
                sat_evidence.append(name + '-exported-model-replay')
            if observation.get('replay', {}).get('result') == 'unsat':
                invalid_models.append(dict(index=row['index'], solver=name))
            if observation.get('unsat_check', {}).get('result') == 'unsat':
                unsat_evidence.append(name + '-independent-unsat-check')
        if observations['z3']['result'] == 'unsat' and any(
                observations[name]['result'] == 'unsat' for name in ('baseline', 'candidate')):
            unsat_evidence.append('independent-z3-xolver-agreement')
        if sat_evidence and unsat_evidence:
            wrong.append(row['index'])
            contradiction = True
        truth = 'sat' if sat_evidence else 'unsat' if unsat_evidence else None
        # A checked witness/certificate establishes truth of the same hashed
        # formula for every timed solver. Do not penalize a solver's verdict
        # solely because a different solver supplied the checked witness.
        verified = {name: truth == o['result'] and truth is not None and not contradiction
                    and o.get('replay', {}).get('result') != 'unsat'
                    for name, o in observations.items()}
        logic = row['case']['logic']
        by_logic.setdefault(logic, {name: Counter() for name in counts})
        for name, observation in observations.items():
            for bucket in (counts[name], by_logic[logic][name]):
                bucket[observation['result']] += 1
                bucket['decided'] += int(observation['result'] in ('sat', 'unsat'))
                bucket['verified_decided'] += int(verified[name])
                bucket['verified_par2'] += observation['seconds'] if verified[name] else 2 * row['timeout']
                bucket['raw_par2'] += observation['seconds'] if observation['result'] in ('sat', 'unsat') else 2 * row['timeout']
        if truth is None and decisive:
            unverified.append(dict(index=row['index'], case=row['case']['member'],
                results={name: o['result'] for name, o in observations.items()},
                reasons={name: o.get('model_error', 'no independent confirmation within budget')
                         for name, o in observations.items() if o['result'] in ('sat', 'unsat')}))
        kind = 'gained' if verified['candidate'] and not verified['baseline'] else (
            'lost' if verified['baseline'] and not verified['candidate'] else 'matched')
        if kind != 'matched':
            comparisons.append(dict(index=row['index'], case=row['case']['member'], kind=kind,
                truth=truth, evidence=sat_evidence or unsat_evidence,
                observations={name: {k: o[k] for k in ('result', 'seconds')}
                              for name, o in observations.items()}))
    return dict(cases=len(reports), binaries=first['binaries'],
                manifest_sha256=first['manifest_sha256'], timeout=first['timeout'],
                memory_bytes=first['memory_bytes'], counts=counts, by_logic=by_logic,
                changes=comparisons, wrong_verdicts=sorted(set(wrong)),
                invalid_exported_models=invalid_models, unverified=unverified,
                scoring='Correct verdicts require a replayed model or an independent UNSAT decision on the identical input hash; unresolved results receive PAR-2 penalty.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--expected-cases', type=int, default=160)
    args = parser.parse_args()
    result = summarize(args.runs, args.expected_cases)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('cases', 'counts', 'changes', 'wrong_verdicts', 'invalid_exported_models')}))
    return int(bool(result['wrong_verdicts'] or result['invalid_exported_models']))


if __name__ == '__main__':
    raise SystemExit(main())
