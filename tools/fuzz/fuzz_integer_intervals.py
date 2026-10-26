#!/usr/bin/env python3
"""Check multivariate integer propagation and replay models with two oracles."""
from itertools import product
import random

from fuzz_linear_arithmetic import arguments, validate_cases
from fuzz_theory_applications import integer


def cases(seed, count):
    rng = random.Random(seed)
    for index in range(count):
        ranges = []
        for _ in range(3):
            lower = rng.randint(-5, 2)
            ranges.append((lower, lower + rng.randint(0, 5)))
        a, b = rng.choice((-5, -2, 1, 3)), rng.choice((-3, -1, 2, 4))
        constant = rng.randint(-4, 4)
        values = [a * x * y + b * z * z + constant
                  for x, y, z in product(*(range(lo, hi + 1) for lo, hi in ranges))]
        commands = ['(declare-const ' + name + ' Int)' for name in ('x', 'y', 'z', 's', 't')]
        for name, (lo, hi) in zip(('x', 'y', 'z'), ranges):
            commands += [f'(assert (<= {integer(lo)} {name}))',
                         f'(assert (<= {name} {integer(hi)}))']
        commands += ['(assert (= s (* x y)))',
                     f'(assert (= t (+ (* {integer(a)} s) (* {integer(b)} z z) {integer(constant)})))']
        if index % 2:
            commands.append(f'(assert (> t {integer(max(values))}))')
            expected = 'unsat'
        else:
            witness = rng.choice(values)
            commands += [f'(assert (<= {integer(witness - 1)} t))',
                         f'(assert (<= t {integer(witness + 1)}))']
            expected = 'sat'
        yield f'interval-{index:04d}', '\n'.join(commands), expected


def main():
    args = arguments(__doc__)
    # An oracle timeout is not a disagreement. Require an independent original
    # verdict, and still require BOTH oracles to replay every exported model.
    return validate_cases(args, cases(args.seed, args.count), 'QF_NIA', require_all_oracles=False)


if __name__ == '__main__':
    raise SystemExit(main())
