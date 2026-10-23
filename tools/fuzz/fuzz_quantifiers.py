#!/usr/bin/env python3
"""Deterministic quantified-domain differential checks with retained input evidence."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import time


def quantify(body, variables, prefix):
    for (name, sort), universal in reversed(list(zip(variables, prefix))):
        body = f'({"forall" if universal else "exists"} (({name} {sort})) {body})'
    return body


def enumerate_prefix(predicate, domains, prefix, values=()):
    if not domains:
        return predicate(*values)
    children = (enumerate_prefix(predicate, domains[1:], prefix[1:], values + (x,))
                for x in domains[0])
    return all(children) if prefix[0] else any(children)


def cases(seed, count):
    rng = random.Random(seed)
    for i in range(count):
        table = rng.randrange(256)
        cubes = ['(and ' + ' '.join(v if mask & (1 << j) else f'(not {v})'
                                    for j, v in enumerate(('a', 'b', 'c'))) + ')'
                 for mask in range(8) if table & (1 << mask)]
        matrix = '(or ' + ' '.join(cubes) + ')' if len(cubes) > 1 else cubes[0] if cubes else 'false'
        prefix = [bool(rng.randrange(2)) for _ in range(3)]
        expected = enumerate_prefix(lambda a, b, c: bool(table & (1 << (a + 2*b + 4*c))),
                                    [range(2)] * 3, prefix)
        yield f'qbf-{i}', quantify(matrix, [(n, 'Bool') for n in ('a', 'b', 'c')], prefix), expected
    operations = ('bvadd', 'bvsub', 'bvmul', 'bvudiv', 'bvurem', 'bvsdiv', 'bvsrem',
                  'bvsmod', 'bvshl', 'bvlshr', 'bvashr', 'bvand', 'bvor', 'bvxor')
    for i in range(count * 2):
        width = rng.choice((1, 2, 3, 4))
        modulus, mask = 1 << width, (1 << width) - 1
        op = operations[i % len(operations)]
        constant = rng.randrange(modulus)
        prefix = [bool(rng.randrange(2)) for _ in range(2)]
        def signed(x):
            return x if x < modulus // 2 else x - modulus
        def value(a, b):
            sa, sb = signed(a), signed(b)
            q = (abs(sa) // abs(sb)) * (-1 if (sa < 0) != (sb < 0) else 1) if sb else 0
            result = {
                'bvadd': lambda: a + b, 'bvsub': lambda: a - b, 'bvmul': lambda: a*b,
                'bvudiv': lambda: a // b if b else mask, 'bvurem': lambda: a % b if b else a,
                'bvsdiv': lambda: q if sb else 1 if sa < 0 else mask,
                'bvsrem': lambda: sa - q*sb if sb else sa,
                'bvsmod': lambda: sa % sb if sb else sa,
                'bvshl': lambda: a << b, 'bvlshr': lambda: a >> b, 'bvashr': lambda: sa >> b,
                'bvand': lambda: a & b, 'bvor': lambda: a | b, 'bvxor': lambda: a ^ b,
            }[op]()
            return result & mask
        relation = rng.choice(('=', 'bvult', 'bvslt'))
        def predicate(a, b):
            result = value(a, b)
            return result == constant if relation == '=' else result < constant if relation == 'bvult' else signed(result) < signed(constant)
        expected = enumerate_prefix(predicate, [range(modulus)] * 2, prefix)
        body = f'({relation} ({op} a b) (_ bv{constant} {width}))'
        yield f'qbv-{i}', quantify(body, [(n, f'(_ BitVec {width})') for n in ('a', 'b')], prefix), expected
    for i in range(count):
        a, b, c = (rng.randrange(-3, 4) for _ in range(3))
        def numeral(x):
            return str(x) if x >= 0 else f'(- {-x})'
        body = f'(= (+ (* {numeral(a)} y y) (* {numeral(b)} x y) {numeral(c)}) 0)'
        # For every real x, a quadratic in y has a real root precisely when
        # a=0 and the x=0 fiber is zero, or a!=0 and its minimum discriminant >=0.
        expected = c == 0 if a == 0 else a*c <= 0
        yield f'real-quadratic-{i}', quantify(body, [('x', 'Real'), ('y', 'Real')], [True, False]), expected
        if i % 4 == 0:
            body = f'(and (= (* x x) 2) (> x 0) (= (* y y) (+ x {numeral(abs(c))})))'
            yield f'real-tower-{i}', quantify(body, [('x', 'Real'), ('y', 'Real')], [False, False]), True


def invoke(command, source, timeout, trailing_args=()):
    start = time.monotonic()
    try:
        p = subprocess.run(command + [str(source)] + list(trailing_args),
                           capture_output=True, text=True, timeout=timeout)
        verdicts = re.findall(r'^(sat|unsat|unknown)\s*$', p.stdout, re.M)
        return dict(verdict=verdicts[0] if p.returncode == 0 and len(verdicts) == 1 else 'error',
                    returncode=p.returncode, stdout=p.stdout, stderr=p.stderr,
                    seconds=time.monotonic() - start)
    except subprocess.TimeoutExpired:
        return dict(verdict='timeout', seconds=time.monotonic() - start)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--count', type=int, default=64)
    parser.add_argument('--seed', type=int, default=20261023)
    parser.add_argument('--timeout', type=float, default=15)
    parser.add_argument('--oracle-timeout', type=float, default=3)
    parser.add_argument('--z3', default=shutil.which('z3'))
    parser.add_argument('--cvc5', default=shutil.which('cvc5'))
    args = parser.parse_args()
    if args.count <= 0 or args.timeout <= 0 or args.oracle_timeout <= 0:
        parser.error('case count and time limits must be positive')
    args.output.mkdir(parents=True, exist_ok=False)
    commands = {'xolver': [str(Path(args.solver).resolve()), 'solve']}
    if args.z3:
        commands['z3'] = [str(Path(args.z3).resolve())]
    if args.cvc5:
        commands['cvc5'] = [str(Path(args.cvc5).resolve()), '--lang=smt2']
    rows, failures, unknowns, oracle_decisions = [], [], [], 0
    for name, formula, expected_bool in cases(args.seed, args.count):
        expected = 'sat' if expected_bool else 'unsat'
        source = args.output / (name + '.smt2')
        source.write_text('(set-logic ALL)\n(assert ' + formula + ')\n(check-sat)\n')
        result = {engine: invoke(command, source, args.timeout if engine == 'xolver' else args.oracle_timeout)
                  for engine, command in commands.items()}
        row = dict(case=name, expected=expected, sha256=hashlib.sha256(source.read_bytes()).hexdigest(), engines=result)
        rows.append(row)
        for engine, answer in result.items():
            actual = answer['verdict']
            if actual in ('sat', 'unsat') and actual != expected or actual == 'error':
                failures.append(dict(case=name, engine=engine, actual=actual, expected=expected))
            if engine == 'xolver' and actual in ('unknown', 'timeout'):
                unknowns.append(dict(case=name, actual=actual))
            if engine != 'xolver' and actual in ('sat', 'unsat'):
                oracle_decisions += 1
        with (args.output / 'cases.jsonl').open('a') as out:
            out.write(json.dumps(row) + '\n')
    summary = dict(seed=args.seed, cases=len(rows), commands=commands,
                   solver_timeout=args.timeout, oracle_timeout=args.oracle_timeout,
                   solver_sha256=hashlib.sha256(Path(args.solver).read_bytes()).hexdigest(),
                   failures=failures, unknowns=unknowns, oracle_decisions=oracle_decisions)
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))
    return int(bool(failures or unknowns))


if __name__ == '__main__':
    raise SystemExit(main())
