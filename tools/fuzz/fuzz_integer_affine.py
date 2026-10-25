#!/usr/bin/env python3
"""Check integer affine solving and complete exported models against Z3/cvc5."""
import random

from fuzz_linear_arithmetic import arguments, validate_cases
from fuzz_theory_applications import integer


def cases(seed, count):
    for negative in (True, False):
        yield 'coprime-bound-' + str(int(negative)), (
            '(declare-const x Int)(declare-const y Int)'
            '(assert (<= (+ (* 4294967296 x) (* 3123612579 y)) 24))'
            '(assert (>= (+ (* 4294967296 x) (* 3123612579 y)) 24))'
            f'(assert ({"<" if negative else ">"} y 0))'), 'sat'
    rng = random.Random(seed)
    for index in range(count):
        a = 2 ** rng.randrange(8, 49)
        b = 2 * rng.randrange(1, 100000) + 1
        if index % 3 == 0:
            a = -a
        if index % 5 == 0:
            b = -b
        expected = 'sat' if index % 2 == 0 else 'unsat'
        rhs = rng.randrange(-32, 33)
        if expected == 'unsat':
            divisor = rng.randrange(2, 9)
            a *= divisor
            b *= divisor
            rhs = divisor * rhs + 1  # gcd(a,b) cannot divide the right-hand side
        form = f'(+ (* {integer(a)} x) (* {integer(b)} y))'
        commands = ['(declare-const x Int)', '(declare-const y Int)']
        if index % 4 < 2:
            commands += [f'(assert (<= {form} {integer(rhs)}))',
                         f'(assert (>= {form} {integer(rhs)}))']
        else:
            commands.append(f'(assert (= {form} {integer(rhs)}))')
        # For coprime coefficients the affine line has infinitely many integer
        # solutions in either direction, so either one-sided bound is feasible.
        commands.append(f'(assert ({"<=" if index % 3 else ">="} y {integer(rng.randrange(-8, 9))}))')
        if index % 3 == 0:
            commands += ['(declare-const z Int)', '(assert (= z (- x y)))']
        if index % 7 == 0:
            commands.append('(assert (distinct y 0))')
        yield f'affine-{index:04d}', '\n'.join(commands), expected


def main():
    args = arguments(__doc__)
    return validate_cases(args, cases(args.seed, args.count), 'QF_LIA')


if __name__ == '__main__':
    raise SystemExit(main())
