#!/usr/bin/env python3
"""Server audit of actual native QE obligations, models and kernel rejection."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

proof = Path(__file__).resolve().parents[1] / 'proof'
if proof.is_dir():
    sys.path.insert(0, str(proof))
from isabelle_pa import Atom, Query, parse
from pa_trace import load, obligations
from replay_pa import replay
from test_pa_isabelle import FIXTURES


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def model(source, output):
    free = Query(source).free
    if not free:
        return None
    result = {}
    def value(expr, sort):
        if sort == 'Bool' and isinstance(expr, Atom) and expr.text in ('true', 'false'):
            return expr.text == 'true'
        if sort == 'Int':
            if isinstance(expr, Atom) and expr.text.isdecimal():
                return int(expr.text)
            if (isinstance(expr, list) and len(expr) == 2 and
                    expr[0] == Atom('-') and isinstance(expr[1], Atom) and expr[1].text.isdecimal()):
                return -int(expr[1].text)
        raise ValueError('nonliteral or ill-typed native PA model')
    def visit(expr):
        if not isinstance(expr, list):
            return
        if expr and expr[0] == Atom('define-fun'):
            if len(expr) != 5 or expr[2] != [] or not isinstance(expr[1], Atom):
                raise ValueError('malformed model binding')
            name = expr[1].text
            if name not in free or name in result or expr[3] != Atom(free[name].sort):
                raise ValueError('unexpected model binding')
            result[name] = value(expr[4], free[name].sort)
        else:
            for child in expr:
                visit(child)
    for expression in parse(output):
        visit(expression)
    if set(result) != set(free):
        raise ValueError('incomplete native PA model')
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--isabelle', type=Path, required=True)
    p.add_argument('--cache', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--include-nary-div', action='store_true', help='Requires the upstream SOMTParser n-ary div fix')
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(__file__, args.output / 'audit_driver.py')
    shutil.copyfile(Path(__file__).with_name('test_pa_isabelle.py'), args.output / 'fixture_driver.py')
    sources = args.output / 'sources'; sources.mkdir()
    claims, observations = [], []
    fixtures = FIXTURES + [
        ('negated-residues', '(assert (forall ((x Int)) (or (= (mod x 2) 0) (= (mod x 2) 1))))', 'sat'),
        ('incompatible-residues', '(assert (exists ((x Int)) (and (= (mod x 6) 2) (= (mod x 4) 1))))', 'unsat'),
        ('free-large-model', '(declare-const x Int)(assert (= (* 3 x) 3000000000000000000000000000003))'
         '(assert (forall ((y Int)) (exists ((z Int)) (= z (+ x y)))))', 'sat')]
    fixtures += [
        ('indexed-divisibility', '(assert (forall ((x Int)) ((_ divisible 1000003) (* 1000003 x))))', 'sat'),
        ('indexed-incompatible-crt', '(assert (exists ((x Int)) (and ((_ divisible 6) (- x 2))'
         ' ((_ divisible 4) (- x 1)))))', 'unsat'),
        ('indexed-exclusion-cover', '(assert (forall ((x Int)) (or ((_ divisible 2) x)'
         ' ((_ divisible 4) (+ x 1)) ((_ divisible 4) (+ x 3)))))', 'sat'),
        ('left-associated-division', '(assert (forall ((x Int))'
         ' (= (div x (- 3) (- 2)) (div (div x (- 3)) (- 2)))))', 'sat'),
        ('crt-counted-free-model', '(declare-const x Int)(assert ((_ divisible 6) (- x 2)))'
         '(assert ((_ divisible 10) (- x 2)))(assert (not ((_ divisible 7) (+ x 1))))'
         '(assert (< x (- 100)))(assert (>= x (- 200)))', 'sat'),
        ('signed-nary-free-model', '(declare-const x Int)(assert (= x (- 13)))'
         '(assert (= (div x (- 3) 2) 2))', 'sat')]
    magnitude = 123456789012345678901234567890123456789012345678901234567890123456789
    numeral = lambda n: str(n) if n >= 0 else f"(- {-n})"
    for sign in (-1, 1):
        value = sign * magnitude
        quotient = value
        for divisor in (1000003, -1000033, 1000037):
            quotient //= abs(divisor)
            if divisor < 0:
                quotient = -quotient
        fixtures.append((f'huge-signed-nary-{sign}', '(declare-const x Int)'
            f'(assert (= x {numeral(value)}))'
            f'(assert (= (div x 1000003 (- 1000033) 1000037) {numeral(quotient)}))', 'sat'))
    pending_parser_cases = [name for name, _, _ in fixtures
                            if not args.include_nary_div and ("nary" in name or name == "left-associated-division")]
    fixtures = [item for item in fixtures if item[0] not in pending_parser_cases]
    (args.output / 'pending-parser-cases.json').write_text(json.dumps(pending_parser_cases, indent=2) + '\n')
    for name, body, expected in fixtures:
        path, cert = sources / (name + '.smt2'), sources / (name + '.json')
        source = '(set-logic LIA)\n' + body + '\n(check-sat)\n'
        path.write_text(source)
        command = [str(args.solver), 'solve', str(path), '--produce-pa-certificate', str(cert), '--produce-models']
        process = subprocess.run(command, capture_output=True, text=True, timeout=45)
        row = dict(input=name, command=command, rc=process.returncode, stdout=process.stdout, stderr=process.stderr,
                   source_sha256=sha(path))
        observations.append(row)
        (args.output / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
        answers = [line for line in process.stdout.splitlines() if line in ('sat', 'unsat', 'unknown')]
        if process.returncode != 0 or answers != [expected] or not cert.is_file():
            raise RuntimeError('native certificate fixture failed: ' + name)
        trace = load(cert.read_text()); obligations(trace, expected)
        row.update(certificate_sha256=sha(cert), steps=len(trace['steps']))
        claim = dict(input=str(path), verdict=expected, certificate=str(cert))
        if expected == 'sat':
            values = model(source, process.stdout)
            if values is not None:
                claim['model'] = values
        claims.append(claim)
    (args.output / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
    (args.output / 'manifest.json').write_text(json.dumps(claims, indent=2) + '\n')
    positive = replay(claims, args.isabelle, args.output / 'accepted', args.cache, 900)
    counts = dict(expected_claims=len(claims), verified_claims=len(claims) if positive['verified'] else 0,
                  qe_steps=sum(row['steps'] for row in observations), models=sum('model' in c for c in claims),
                  false_step_rejected=0, false_model_rejected=0, solver_sha256=sha(args.solver))
    if positive['verified']:
        # An actual inner quantifier obligation is falsified, while the native
        # verdict, final Boolean and original input all remain unchanged.
        tampered = copy.deepcopy(load(Path(claims[0]['certificate']).read_text()))
        if tampered['steps'][0]['after'] != [[]]:
            raise RuntimeError('negative control precondition changed')
        tampered['steps'][0]['after'] = []
        bad_path = sources / 'false-step.json'; bad_path.write_text(json.dumps(tampered, indent=2) + '\n')
        bad_step = dict(claims[0], certificate=str(bad_path))
        bad_model = dict(claims[-1], model={'x': 0})
        for name, claim, metric in [('false-step', bad_step, 'false_step_rejected'),
                                    ('false-model', bad_model, 'false_model_rejected')]:
            report = replay([claim], args.isabelle, args.output / name, args.cache, 180)
            log = (args.output / name / 'isabelle.log').read_text()
            counts[metric] = int(report['returncode'] not in (0, 124) and
                ('Failed to apply initial proof method' in log or 'Failed to finish proof' in log))
    counts['passed'] = int(counts['verified_claims'] == len(claims) and
                           counts['false_step_rejected'] == counts['false_model_rejected'] == 1)
    (args.output / 'metrics.json').write_text(json.dumps(counts, indent=2) + '\n')
    if os.environ.get('EOS_METRICS_FILE'):
        Path(os.environ['EOS_METRICS_FILE']).write_text(json.dumps(counts) + '\n')
    print(json.dumps(counts))
    return not counts['passed']


if __name__ == '__main__':
    raise SystemExit(main())
