#!/usr/bin/env python3
"""Check signed QF_LRA formulas and exported models against Z3 and cvc5."""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

from fuzz_quantifiers import invoke
from fuzz_theory_applications import replay


def rational(value):
    value = Fraction(value)
    numerator = str(value.numerator) if value >= 0 else f'(- {-value.numerator})'
    return numerator if value.denominator == 1 else f'(/ {numerator} {value.denominator})'


def linear(coefficients):
    terms = [f'(* {rational(coefficient)} x{index})'
             for index, coefficient in enumerate(coefficients) if coefficient]
    return terms[0] if len(terms) == 1 else '(+ ' + ' '.join(terms) + ')'


def cases(seed, count):
    for lower in (True, False):
        yield 'negative-target-' + ('lower' if lower else 'upper'), (
            '(declare-const x0 Real)(declare-const x1 Real)'
            f'(assert ({">=" if lower else "<="} (- x1 x0) 0))'
            f'(assert (>= x1 {0 if lower else "(- 10)"}))'
            f'(assert (<= x1 {10 if lower else 0}))'
            f'(assert (= x0 {5 if lower else "(- 5)"}))'), 'sat'
    rng = random.Random(seed)
    for index in range(count):
        size = rng.randrange(2, 5)
        witness = [Fraction(rng.randrange(-6, 7), 3) for _ in range(size)]
        commands = [f'(declare-const x{v} Real)' for v in range(size)]
        for v in range(size):
            commands += [f'(assert (>= x{v} (- 4)))', f'(assert (<= x{v} 4))']
        for atom in range(rng.randrange(4, 11)):
            coefficients = [Fraction(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randrange(1, 4))
                            for _ in range(size)]
            value = sum((a * b for a, b in zip(coefficients, witness)), Fraction(0))
            margin = Fraction(rng.randrange(1, 4), rng.randrange(1, 4))
            relation = rng.choice(('<=', '>=', '<', '>', '=', 'distinct'))
            rhs = value + margin if relation in ('<=', '<', 'distinct') else (
                value - margin if relation in ('>=', '>') else value)
            term = linear(coefficients)
            true_atom = f'({relation} {term} {rational(rhs)})'
            if atom % 3 == 0:
                # At least one branch holds at the independently chosen witness.
                other = f'(< {term} {rational(-rhs)})'
                commands.append(f'(assert (or {true_atom} {other}))')
            else:
                commands.append(f'(assert {true_atom})')
        expected = 'sat' if index % 2 == 0 else 'unsat'
        if expected == 'unsat':
            term = linear([Fraction(2), Fraction(-3)] + [Fraction(0)] * (size - 2))
            threshold = rational(Fraction(rng.randrange(-4, 5), 3))
            commands += ['(declare-const p Bool)', f'(assert (<= {term} {threshold}))',
                         f'(assert (or p (> {term} {threshold})))',
                         f'(assert (or (not p) (> {term} {threshold})))']
        yield f'signed-{index:04d}', '\n'.join(commands), expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--z3', type=Path, required=True)
    parser.add_argument('--cvc5', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--count', type=int, default=128)
    parser.add_argument('--seed', type=int, default=20261025)
    parser.add_argument('--timeout', type=float, default=5)
    args = parser.parse_args()
    if args.count <= 0 or args.timeout <= 0:
        parser.error('positive count and timeout are required')
    args.output.mkdir(parents=True, exist_ok=False)
    commands = {'xolver': [str(args.solver.resolve()), 'solve'],
                'z3': [str(args.z3.resolve())],
                'cvc5': [str(args.cvc5.resolve()), '--lang=smt2']}
    failures, models, total = [], 0, 0
    for name, body, expected in cases(args.seed, args.count):
        prefix = '(set-logic QF_LRA)\n(set-option :produce-models true)\n' + body + '\n'
        source = args.output / (name + '.smt2')
        source.write_text(prefix + '(check-sat)\n')
        results = {engine: invoke(command, source, args.timeout) for engine, command in commands.items()}
        row = dict(case=name, expected=expected, sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   engines=results)
        total += 1
        for engine, result in results.items():
            if result['verdict'] != expected:
                failures.append(dict(case=name, engine=engine, expected=expected, actual=result['verdict']))
        if results['xolver']['verdict'] == 'sat':
            query = args.output / (name + '-model.smt2')
            query.write_text(prefix + '(check-sat)(get-model)\n')
            model = invoke(commands['xolver'], query, args.timeout)
            row['model'] = model
            try:
                if model['verdict'] != 'sat':
                    raise ValueError('model query failed')
                pinned = args.output / (name + '-replay.smt2')
                pinned.write_text(replay(prefix, model['stdout']))
                checked = {engine: invoke(command, pinned, args.timeout)
                           for engine, command in commands.items() if engine != 'xolver'}
                row['replay'] = checked
                for engine, result in checked.items():
                    if result['verdict'] != 'sat':
                        failures.append(dict(case=name, engine=engine, model=result['verdict']))
                models += 1
            except ValueError as error:
                row['model_error'] = str(error)
                failures.append(dict(case=name, model_error=str(error)))
        with (args.output / 'cases.jsonl').open('a') as stream:
            stream.write(json.dumps(row) + '\n')
    binaries = {name: dict(path=command[0], sha256=hashlib.sha256(Path(command[0]).read_bytes()).hexdigest())
                for name, command in commands.items()}
    for engine in ('z3', 'cvc5'):
        version = subprocess.run([commands[engine][0], '--version'], capture_output=True, text=True, timeout=10)
        binaries[engine]['version'] = version.stdout.splitlines()[0] if version.stdout else version.stderr[:200]
    summary = dict(cases=total, models=models, failures=failures, seed=args.seed, binaries=binaries)
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    metrics = dict(cases=total, models=models, failures=len(failures))
    (args.output / 'metrics.json').write_text(json.dumps(metrics) + '\n')
    if os.environ.get('EOS_METRICS_FILE'):
        Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics) + '\n')
    print(json.dumps(metrics))
    return int(bool(failures) or not models)


if __name__ == '__main__':
    raise SystemExit(main())
