#!/usr/bin/env python3
"""Differential native-theory queries and independent replay of exported models."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys

from fuzz_quantifiers import invoke

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'proof'))
from isabelle_pa import Atom, parse


def emit(node):
    if isinstance(node, list):
        return '(' + ' '.join(map(emit, node)) + ')'
    if not isinstance(node, Atom):
        raise ValueError('invalid model syntax')
    if node.kind == 'string':
        return '"' + node.text.replace('"', '""') + '"'
    return '|' + node.text + '|' if node.kind == 'quoted' else node.text


def replay(prefix, output):
    expressions = parse(output)
    if len(expressions) != 2 or emit(expressions[0]) != 'sat':
        raise ValueError('expected SAT followed by exactly one model')
    bindings = expressions[1]
    if not isinstance(bindings, list):
        raise ValueError('expected model bindings')
    if bindings and isinstance(bindings[0], Atom) and emit(bindings[0]) == 'model':
        bindings = bindings[1:]
    definitions = {}
    for binding in bindings:
        if (not isinstance(binding, list) or len(binding) != 5
                or emit(binding[0]) != 'define-fun'):
            raise ValueError('unsupported model binding')
        name = emit(binding[1])
        if name in definitions:
            raise ValueError('duplicate model definition')
        definitions[name] = binding
    commands = []
    for command in parse(prefix):
        op = emit(command[0])
        if op in ('declare-const', 'declare-fun'):
            name = emit(command[1])
            if name not in definitions:
                raise ValueError('missing interpretation for ' + name)
            binding = definitions[name]
            args, result = ([], command[2]) if op == 'declare-const' else (command[2], command[3])
            if (emit(result) != emit(binding[3]) or len(args) != len(binding[2])
                    or any(emit(a) != emit(b[1]) for a, b in zip(args, binding[2]))):
                raise ValueError('model signature mismatch for ' + name)
            commands.append(emit(binding))
        else:
            commands.append(emit(command))
    return '\n'.join(commands) + '\n(check-sat)\n'


def integer(n):
    return str(n) if n >= 0 else f'(- {-n})'


def string(s):
    return '"' + ''.join('""' if c == '"' else c if 32 <= ord(c) <= 126 and c != '\\'
                         else f'\\u{{{ord(c):x}}}' for c in s) + '"'


def fp_value(bits):
    # Five-bit encoding: sign=1, exponent=2, trailing significand=2.
    sign, exponent, fraction = bits >> 4, (bits >> 2) & 3, bits & 3
    if exponent == 3:
        return None if fraction else float('-inf') if sign else float('inf')
    value = fraction / 4 if exponent == 0 else (1 + fraction / 4) * 2 ** (exponent - 1)
    return -value if sign else value


def cases(seed, count):
    rng = random.Random(seed)
    for i in range(count * 2):
        a, b = rng.randrange(32), rng.randrange(32)
        va, vb = fp_value(a), fp_value(b)
        op = ('fp.eq', 'fp.lt', 'fp.leq', 'fp.gt', 'fp.geq', '=')[i % 6]
        expected = (va is None and vb is None or a == b) if op == '=' else (
            va is not None and vb is not None and {
                'fp.eq': lambda: va == vb, 'fp.lt': lambda: va < vb,
                'fp.leq': lambda: va <= vb, 'fp.gt': lambda: va > vb,
                'fp.geq': lambda: va >= vb}[op]())
        prefix = ('(declare-const x (_ FloatingPoint 2 3))'
                  '(declare-const y (_ FloatingPoint 2 3))'
                  f'(assert (= x ((_ to_fp 2 3) (_ bv{a} 5))))'
                  f'(assert (= y ((_ to_fp 2 3) (_ bv{b} 5))))'
                  f'(assert ({op} x y))')
        yield f'fp-order-{i}', prefix, expected
    for bits in range(32):
        sign, exponent, fraction = bits >> 4, (bits >> 2) & 3, bits & 3
        predicates = [('fp.isNaN', exponent == 3 and fraction != 0),
                      ('fp.isInfinite', exponent == 3 and fraction == 0),
                      ('fp.isZero', exponent == 0 and fraction == 0),
                      ('fp.isNormal', exponent not in (0, 3)),
                      ('fp.isSubnormal', exponent == 0 and fraction != 0),
                      ('fp.isNegative', bool(sign) and not (exponent == 3 and fraction != 0)),
                      ('fp.isPositive', not sign and not (exponent == 3 and fraction != 0))]
        expected = predicates[bits % len(predicates)][1]
        op = predicates[bits % len(predicates)][0]
        yield f'fp-class-{bits}', ('(declare-const x (_ FloatingPoint 2 3))'
                                  f'(assert (= x ((_ to_fp 2 3) (_ bv{bits} 5))))'
                                  f'(assert ({op} x))'), expected
    # Every free result is checked by replaying the emitted interpretation in
    # both external solvers; satisfiability alone would not test rounding.
    formats = [(2, 3), (3, 4), (5, 11), (8, 24)]
    rounding = ['RNE', 'RNA', 'RTP', 'RTN', 'RTZ']
    for i in range(count * 5):
        e, precision = formats[i % len(formats)]
        width = e + precision
        a, b = rng.randrange(1 << width), rng.randrange(1 << width)
        operation = ['fp.add', 'fp.sub', 'fp.mul', 'fp.div'][(i // 5) % 4]
        mode = rounding[i % 5]
        ty = f'(_ FloatingPoint {e} {precision})'
        x = f'((_ to_fp {e} {precision}) (_ bv{a} {width}))'
        y = f'((_ to_fp {e} {precision}) (_ bv{b} {width}))'
        prefix = (f'(declare-const x {ty})(declare-const y {ty})(declare-const result {ty})'
                  f'(assert (= x {x}))(assert (= y {y}))'
                  f'(assert (= result ({operation} {mode} x y)))')
        yield f'fp-arithmetic-{i}', prefix, True
    for mode in rounding:
        for operation in ['fp.add', 'fp.sub', 'fp.mul', 'fp.div']:
            for a, b in [(0, 0), (16, 0), (0, 16), (16, 16), (12, 28),
                         (12, 0), (1, 8), (11, 8), (13, 4), (4, 20)]:
                prefix = ('(declare-const result (_ FloatingPoint 2 3))'
                          f'(assert (= result ({operation} {mode}'
                          f' ((_ to_fp 2 3) (_ bv{a} 5)) ((_ to_fp 2 3) (_ bv{b} 5)))))')
                yield f'fp-edge-{operation}-{mode}-{a}-{b}', prefix, True
    yield 'fp-symbolic-rounding', ('(declare-const mode RoundingMode)'
        '(declare-const result (_ FloatingPoint 2 3))'
        '(assert (distinct mode RTZ))'
        '(assert (= result (fp.add mode (fp #b0 #b01 #b00) (fp #b0 #b00 #b01))))'), True
    for i in range(count):
        a, b, c = (rng.randrange(8) for _ in range(3))
        yield f'uf-{i}', ('(declare-fun f ((_ BitVec 3)) (_ BitVec 3))'
                          '(declare-const x (_ BitVec 3))'
                          f'(assert (= x (_ bv{a} 3)))'
                          f'(assert (= (f x) (_ bv{b} 3)))'
                          f'(assert (= (f (_ bv{a} 3)) (_ bv{c} 3)))'), b == c
        index, value = rng.randrange(4), rng.randrange(8)
        yield f'array-{i}', ('(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))'
                             '(declare-const b (Array (_ BitVec 2) (_ BitVec 3)))'
                             f'(assert (= a ((as const (Array (_ BitVec 2) (_ BitVec 3))) (_ bv{b} 3))))'
                             f'(assert (= b (store a (_ bv{index} 2) (_ bv{value} 3))))'
                             f'(assert (= (select b (_ bv{index} 2)) (_ bv{c} 3)))'), value == c
    words = ['', 'a', 'abba', '007', 'a"b', '\\u', '\U0001f600a', '\x00']
    for i in range(count * 2):
        a, b = rng.choice(words), rng.choice(words)
        start, length = rng.randrange(-1, len(a) + 2), rng.randrange(-1, 5)
        operations = [
            (f'(str.len s)', str(len(a))),
            (f'(str.++ s {string(b)})', string(a + b)),
            (f'(str.substr s {integer(start)} {integer(length)})',
             string(a[start:start + length] if start >= 0 and length > 0 else '')),
            (f'(str.indexof s {string(b)} {integer(start)})',
             integer(a.find(b, start) if 0 <= start <= len(a) else -1)),
            (f'(str.contains s {string(b)})', str(b in a).lower()),
            (f'(str.replace s {string(b)} "z")', string(a.replace(b, 'z', 1))),
            (f'(str.replace_all s {string(b)} "z")', string(a.replace(b, 'z') if b else a)),
            ('(str.to_int s)', integer(int(a) if a and all('0' <= c <= '9' for c in a) else -1)),
        ]
        term, value = operations[i % len(operations)]
        relation = '=' if i % 3 else 'distinct'
        yield f'string-{i}', (f'(declare-const s String)(assert (= s {string(a)}))'
                              f'(assert ({relation} {term} {value}))'), relation == '='
    for i, a in enumerate(words):
        yield f'regex-{i}', (f'(declare-const s String)(assert (= s {string(a)}))'
                             '(assert (str.in_re s (re.* (re.union (str.to_re "a")'
                             ' (str.to_re "b")))))'), all(c in 'ab' for c in a)
    yield 'free-fp', ('(declare-const x (_ FloatingPoint 8 24))(declare-const unused RoundingMode)'
                      '(assert (fp.isSubnormal x))'), True
    yield 'free-string', '(declare-const s String)(assert (str.contains s "abc"))', True
    yield 'empty-string', '(declare-const s String)(assert (= (str.len s) 0))', True
    yield 'free-array', ('(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))'
                         '(assert (= (select a #b00) #b101))(assert (= (select a #b11) #b011))'), True
    yield 'free-uf', ('(declare-fun f ((_ BitVec 3)) (_ BitVec 3))'
                      '(assert (= (f #b000) #b101))(assert (= (f #b001) #b011))'), True
    yield 'bool-array', ('(declare-const a (Array Bool Bool))'
                        '(assert (select a true))(assert (not (select a false)))'), True
    yield 'constant-integer-uf', ('(declare-fun f (Int) Int)'
                                 '(assert (= (f 2) 4))'), True
    yield 'constant-integer-uf-conflict', ('(declare-fun f (Int) Int)'
                                          '(assert (= (f 2) 4))(assert (= (f 2) 5))'), False
    yield 'constant-real-uf', ('(declare-fun f (Real) Real)'
                               '(assert (= (f 2.0) (/ 1.0 2.0)))'), True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--count', type=int, default=32)
    parser.add_argument('--seed', type=int, default=20261023)
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--z3', default=shutil.which('z3'))
    parser.add_argument('--cvc5', default=shutil.which('cvc5'))
    args = parser.parse_args()
    if args.count <= 0 or args.timeout <= 0 or not args.z3 or not args.cvc5:
        parser.error('positive count/timeout and both independent oracles are required')
    args.output.mkdir(parents=True, exist_ok=False)
    commands = {'xolver': [str(args.solver.resolve()), 'solve'],
                'z3': [str(Path(args.z3).resolve())],
                'cvc5': [str(Path(args.cvc5).resolve()), '--lang=smt2']}
    failures, total, models = [], 0, 0
    for name, body, expected_bool in cases(args.seed, args.count):
        expected = 'sat' if expected_bool else 'unsat'
        prefix = '(set-logic ALL)\n(set-option :produce-models true)\n' + body + '\n'
        source = args.output / (name + '.smt2')
        source.write_text(prefix + '(check-sat)\n')
        results = {engine: invoke(command, source, args.timeout,
                                  ('--verbose',) if engine == 'xolver' else ())
                   for engine, command in commands.items()}
        row = dict(case=name, expected=expected, sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   engines=results)
        total += 1
        for engine, result in results.items():
            if result['verdict'] != expected:
                failures.append(dict(case=name, engine=engine, expected=expected, actual=result['verdict']))
        if results['xolver']['verdict'] == 'unknown':
            diagnostic = subprocess.run(commands['xolver'] + [str(source), '--features'],
                                        capture_output=True, text=True, timeout=args.timeout)
            row['features'] = dict(stdout=diagnostic.stdout, stderr=diagnostic.stderr,
                                   returncode=diagnostic.returncode)
        if results['xolver']['verdict'] == 'sat':
            query = args.output / (name + '-model.smt2')
            query.write_text(prefix + '(check-sat)(get-model)\n')
            candidate = invoke(commands['xolver'], query, args.timeout, ('--verbose',))
            row['model'] = candidate
            try:
                if candidate['verdict'] != 'sat':
                    raise ValueError('model query failed')
                pinned = args.output / (name + '-replay.smt2')
                pinned.write_text(replay(prefix, candidate['stdout']))
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
    summary = dict(cases=total, models=models, failures=failures, commands=commands, seed=args.seed,
                   solver_sha256=hashlib.sha256(args.solver.read_bytes()).hexdigest())
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))
    return int(bool(failures) or not models)


if __name__ == '__main__':
    raise SystemExit(main())
