#!/usr/bin/env python3
"""Replay Boolean SL through arithmetic using the bijection x -> x+1, y -> y+1."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('solver', 'helpers', 'corpus', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=15)
    args = parser.parse_args()
    sys.path.insert(0, str(args.helpers.resolve()))
    from fuzz_presburger import invoke
    from fuzz_native_separation import Atom, emit, parse
    args.output.mkdir(parents=True, exist_ok=False)
    for source in [Path(__file__).resolve(), args.helpers / 'fuzz_presburger.py',
                   args.helpers / 'fuzz_native_separation.py',
                   args.helpers.parent / 'proof/isabelle_pa.py', args.helpers.parent / 'proof/pa_trace.py']:
        target = args.output / 'driver' / source.parent.name / source.name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)

    def shifted(node):
        if isinstance(node, Atom):
            return [Atom('+'), node, Atom('1')] if node.text in ('x', 'y') else node
        return [shifted(child) for child in node]

    counts = dict(cases=0, mismatches=0, unknown=0, errors=0, timeouts=0,
                  baseline_inconclusive=0, models=0, model_rejections=0)
    records = []
    for index, expected in enumerate(json.loads((args.corpus / 'candidate.json').read_text())):
        original = args.output / f'original-{index:04}.smt2'
        shutil.copyfile(args.corpus / expected['input'], original)
        commands = []
        for command in parse(original.read_text()):
            if command[0] == Atom('check-sat'):
                continue
            if command[0] == Atom('assert'):
                command = [command[0], shifted(command[1])]
            commands.append(emit(command))
        # This independent, satisfiable constraint forces the arithmetic path
        # even for formulas mentioning no integer terms (e.g. emp or false).
        commands.extend(['(declare-const @xolver.metamorphic Int)',
                         '(assert (> @xolver.metamorphic 0))', '(check-sat)', '(get-model)'])
        query = args.output / f'shifted-{index:04}.smt2'
        query.write_text('\n'.join(commands) + '\n')
        baseline = invoke([str(args.solver), 'solve', str(original)], args.timeout)
        candidate = invoke([str(args.solver), 'solve', str(query), '--check-model', '--verbose'], args.timeout)
        counts['cases'] += 1
        result = candidate['result']
        if baseline['result'] not in ('sat', 'unsat') or expected['result'] not in ('sat', 'unsat'):
            counts['baseline_inconclusive'] += 1
        else:
            counts['mismatches'] += baseline['result'] != expected['result'] or (
                result in ('sat', 'unsat') and result != baseline['result'])
        for outcome, key in [('unknown', 'unknown'), ('error', 'errors'), ('timeout', 'timeouts')]:
            counts[key] += result == outcome
        counts['models'] += result == 'sat'
        counts['model_rejections'] += 'MODEL_MISMATCH' in candidate.get('stderr', '')
        records.append(dict(index=index, original=original.name, original_sha256=sha(original),
                            query=query.name, query_sha256=sha(query), library=expected['result'],
                            baseline=baseline, candidate=candidate))
        (args.output / 'progress.json').write_text(json.dumps(counts) + '\n')
    report = dict(metrics=counts, records=records, solver_sha256=sha(args.solver),
                  corpus_sha256=sha(args.corpus / 'candidate.json'))
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    (args.output / 'metrics.json').write_text(json.dumps(counts) + '\n')
    if os.environ.get('EOS_METRICS_FILE'):
        Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(counts) + '\n')
    print(json.dumps(counts))
    return int(counts['cases'] != 240 or not counts['models'] or
               any(v for k, v in counts.items() if k not in ('cases', 'models')))


if __name__ == '__main__':
    raise SystemExit(main())
