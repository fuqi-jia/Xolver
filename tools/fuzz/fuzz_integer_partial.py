#!/usr/bin/env python3
"""Check integer partial arithmetic and pin exported zero-divisor interpretations."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess

from fuzz_quantifiers import invoke
from fuzz_theory_applications import Atom, emit, integer, parse, replay


def replay_integer_model(prefix, output):
    forms = parse(output)
    if len(forms) != 2 or emit(forms[0]) != 'sat' or not isinstance(forms[1], list):
        raise ValueError('expected SAT and one model')
    bindings = forms[1]
    if bindings and isinstance(bindings[0], Atom) and emit(bindings[0]) == 'model':
        bindings = bindings[1:]
    definitions = {emit(b[1]): b for b in bindings
                   if isinstance(b, list) and len(b) == 5 and emit(b[0]) == 'define-fun'}
    aliases = {'div': '|xolver.model.div!|', 'mod': '|xolver.model.mod!|'}
    extensions = []
    for op, alias in aliases.items():
        if op in definitions:
            definition = definitions[op]
            if (emit(definition[3]) != 'Int' or len(definition[2]) != 2
                    or any(emit(a[1]) != 'Int' for a in definition[2])):
                raise ValueError('invalid integer partial-function signature')
            args, body = emit(definition[2]), emit(definition[4])
        else:
            # Xolver's explicitly selected extension has default zero. Do not
            # let an oracle choose a different interpretation for an absent row.
            args, body = '((a Int) (b Int))', f'(ite (= b 0) 0 ({op} a b))'
        extensions.append(f'(define-fun {alias} {args} Int {body})')

    def renamed(node):
        if not isinstance(node, list):
            return emit(node)
        if not node:
            return '()'
        head = emit(node[0])
        return '(' + aliases.get(head, head) + ''.join(' ' + renamed(x) for x in node[1:]) + ')'

    commands = [renamed(c) for c in parse(prefix) if emit(c[0]) != 'set-logic']
    lowered = '(set-logic ALL)\n' + '\n'.join(extensions + commands) + '\n'
    return replay(lowered, output)


def cases(seed, count):
    rng = random.Random(seed)
    for i in range(count):
        a, k, b = rng.randint(-4, 4), rng.randint(-5, 5), rng.randint(1, 4)
        op = 'div' if i % 2 else 'mod'
        logic = ('QF_NIA', 'ALL')[i % 2]
        x = '(declare-const x Int)'
        xy = x + '(declare-const y Int)'
        yield f'zero-value-{i}', logic, (x + f'(assert (or (= x {integer(a)}) (= x {integer(a+1)})))'
            f'(assert (= ({op} x 0) {integer(k)}))'), 'sat'
        yield f'zero-congruence-{i}', 'QF_NIA', (xy + '(assert (= x y))'
            f'(assert (not (= ({op} (+ x 1) 0) ({op} (+ y 1) 0))))'), 'unsat'
        yield f'zero-distinct-{i}', 'QF_NIA', (xy + '(assert (distinct x y))'
            f'(assert (= ({op} x 0) {integer(k)}))(assert (= ({op} y 0) {integer(k+1)}))'), 'sat'
        xd = x + '(declare-const d Int)'
        signed = b if i % 2 else -b
        q = a // abs(signed)
        if signed < 0:
            q = -q
        lo, hi = (signed, signed+1) if signed > 0 else (signed-1, signed)
        yield f'variable-sign-{i}', 'QF_NIA', (xd +
            f'(assert (and (<= {integer(a)} x) (<= x {integer(a+1)})'
            f'(<= {integer(lo)} d) (<= d {integer(hi)})))'
            f'(assert (= (div x d) {integer(q)}))'), 'sat'
        yield f'remainder-range-{i}', 'QF_NIA', (xd +
            f'(assert (and (<= {integer(a)} x) (<= x {integer(a+1)})'
            f'(<= {b} d) (<= d {b+1})))'
            '(assert (>= (mod x d) d))'), 'unsat'
        yield f'optional-zero-{i}', 'QF_NIA', (xd +
            f'(assert (or (= d 0) (= d {b})))(assert (= x {integer(a)}))'
            f'(assert (= ({op} x d) {integer(k)}))'), 'sat'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--z3', type=Path, required=True)
    p.add_argument('--cvc5', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seed', type=int, default=20261025)
    p.add_argument('--count', type=int, default=4)
    p.add_argument('--timeout', type=float, default=5)
    args = p.parse_args()
    if args.count <= 0 or args.timeout <= 0:
        p.error('count and timeout must be positive')
    args.output.mkdir(parents=True, exist_ok=False)
    commands = {'xolver': [str(args.solver.resolve()), 'solve'],
                'z3': [str(args.z3.resolve())],
                'cvc5': [str(args.cvc5.resolve()), '--lang=smt2']}
    failures, rows, models = [], [], 0
    for name, logic, body, expected in cases(args.seed, args.count):
        prefix = f'(set-logic {logic})\n' + body + '\n'
        source = args.output / (name + '.smt2')
        source.write_text(prefix + '(check-sat)\n')
        results = {engine: invoke(command, source, args.timeout) for engine, command in commands.items()}
        row = dict(name=name, expected=expected, engines=results,
                   source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
        for engine, result in results.items():
            if result['verdict'] != expected:
                failures.append(dict(name=name, engine=engine, verdict=result['verdict'], expected=expected))
        if results['xolver']['verdict'] == 'sat':
            model_file = args.output / (name + '-model.smt2')
            model_file.write_text(prefix + '(check-sat)(get-model)\n')
            model = invoke(commands['xolver'], model_file, args.timeout)
            row['model'] = model
            try:
                pinned = args.output / (name + '-replay.smt2')
                pinned.write_text(replay_integer_model(prefix, model.get('stdout', '')))
                row['replay'] = {engine: invoke(command, pinned, args.timeout)
                                 for engine, command in commands.items() if engine != 'xolver'}
                for engine, result in row['replay'].items():
                    if result['verdict'] != 'sat':
                        failures.append(dict(name=name, engine=engine, model=result['verdict']))
                models += 1
            except ValueError as error:
                row['model_error'] = str(error)
                failures.append(dict(name=name, model_error=str(error)))
        rows.append(row)
        (args.output / 'progress.json').write_text(json.dumps(dict(completed=len(rows), total=args.count*6)))
    negative_prefix = '(declare-const x Int)(assert (= x 2))(assert (= (div x 0) 7))'
    for label, extra in [('wrong-zero-value', '(define-fun div ((a Int)(b Int)) Int (ite (= b 0) 8 (div a b)))'),
                         ('missing-zero-value', '')]:
        pinned = args.output / (label + '.smt2')
        pinned.write_text(replay_integer_model(negative_prefix,
            'sat\n((define-fun x () Int 2)' + extra + ')'))
        for engine in ['z3','cvc5']:
            result = invoke(commands[engine], pinned, args.timeout)
            rows.append(dict(name=label, engine=engine, negative_control=result))
            if result['verdict'] != 'unsat':
                failures.append(dict(name=label, engine=engine, verdict=result['verdict']))
    report = dict(cases=args.count*6, models=models, failures=failures, rows=rows, seed=args.seed,
        binaries={n:dict(path=c[0],sha256=hashlib.sha256(Path(c[0]).read_bytes()).hexdigest())
                  for n,c in commands.items()})
    (args.output / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    metrics = dict(cases=report['cases'], models=models, failures=len(failures))
    (args.output / 'metrics.json').write_text(json.dumps(metrics)+'\n')
    if os.environ.get('EOS_METRICS_FILE'):
        Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(metrics)+'\n')
    print(json.dumps({k:report[k] for k in ('cases','models','failures')}))
    return int(bool(failures) or models == 0)


if __name__ == '__main__':
    raise SystemExit(main())
