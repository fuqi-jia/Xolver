#!/usr/bin/env python3
"""Independent signed/zero arithmetic checks for the Rocq source adapter."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import integer, parse


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--z3', type=Path, required=True)
    p.add_argument('--sv', type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    equations = []
    for a in range(-9, 10):
        for b in range(-4, 5):
            q = 0 if b == 0 else (abs(a) // abs(b)) * (-1 if (a < 0) != (b < 0) else 1)
            floor = 0 if b == 0 else a // b
            for op, expected in [('÷', q), ('%', a - b * q), ('/', floor), ('Z.modulo', a - b * floor)]:
                source = f'({a}) {op} ({b})' if op != 'Z.modulo' else f'Z.modulo ({a}) ({b})'
                term = parse(source, {})
                equations.append(f'(= {term.smt} {integer(expected)})')
    source = '(set-logic ALL)\n(assert (not (and ' + ' '.join(equations) + ')))\n(check-sat)\n'
    query = args.output / 'arithmetic.smt2'
    query.write_text(source)
    report = {'equations': len(equations), 'results': {}}
    for name, command in [('xolver', [str(args.solver), 'solve', str(query)]),
                          ('z3', [str(args.z3), str(query)]), ('sv', [str(args.sv), str(query)])]:
        ran = subprocess.run(command, text=True, capture_output=True, timeout=60)
        report['results'][name] = {'returncode': ran.returncode, 'stdout': ran.stdout, 'stderr': ran.stderr}
        good = ran.stdout.strip() == 'unsat' if name != 'sv' else json.loads(ran.stdout)['status'] == 'valid'
        if ran.returncode or not good:
            (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
            raise RuntimeError(f'{name}: arithmetic semantics check failed')
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'equations': len(equations), 'failures': 0}))


if __name__ == '__main__':
    main()
