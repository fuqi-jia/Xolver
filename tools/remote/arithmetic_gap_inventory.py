#!/usr/bin/env python3
"""Join frozen arithmetic runs by input hash, retaining confirmation boundaries."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def reports(directory):
    rows = {}
    for report in sorted(directory.glob('lane-*/report.json')):
        data = json.loads(report.read_text())
        for row in data['rows']:
            key = row['case']['sha256']
            if key in rows:
                raise ValueError('duplicate input hash: ' + key)
            rows[key] = dict(row, evidence_path=str(report))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--oracle', default='z3_current')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    baseline, candidate = reports(args.baseline), reports(args.candidate)
    if baseline.keys() != candidate.keys():
        raise ValueError('runs do not cover the same input hashes')
    gaps, unknown_status, contradictions = [], [], []
    for sha, row in sorted(candidate.items(), key=lambda item: item[1]['index']):
        case = row['case']
        actual = hashlib.sha256(Path(case['path']).read_bytes()).hexdigest()
        if actual != sha:
            raise ValueError('input changed: ' + case['path'])
        original = baseline[sha]
        oracle = original['observations'][args.oracle]
        observation = row['observations']['xolver']
        detail = dict(index=row['index'], case=case, xolver=observation,
                      oracle=oracle, oracle_evidence=original['evidence_path'])
        decisive = ('sat', 'unsat')
        if observation['result'] not in decisive and oracle['result'] in decisive:
            gaps.append(detail)
        if observation['result'] in decisive and oracle['result'] in decisive:
            if observation['result'] != oracle['result']:
                contradictions.append(detail)
        if case.get('expected', 'unknown') == 'unknown' and observation['result'] in decisive:
            detail['independent_verdict_agrees'] = oracle['result'] == observation['result']
            detail['model_replay_checked'] = False
            unknown_status.append(detail)
    result = dict(gaps=gaps, unknown_status_decisions=unknown_status,
                  contradictions=contradictions,
                  by_logic=dict(Counter(row['case']['logic'] for row in gaps)),
                  by_family=dict(Counter(row['case']['logic'] + '/' + row['case']['family'] for row in gaps)),
                  policy='Hash-matched historical oracle verdicts; SAT model replay is a separate check.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(cases=len(candidate), gaps=len(gaps),
                         unknown_status_decisions=len(unknown_status),
                         contradictions=len(contradictions), by_logic=result['by_logic'])))
    return int(bool(contradictions))


if __name__ == '__main__':
    raise SystemExit(main())
