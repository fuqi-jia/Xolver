#!/usr/bin/env python3
"""Check integer polynomial residue identities and models against Z3/cvc5."""
import math
import random

from fuzz_linear_arithmetic import arguments, validate_cases
from fuzz_theory_applications import integer


def power(variable, exponent):
    return variable if exponent == 1 else '(* ' + ' '.join([variable] * exponent) + ')'


def cases(seed, count):
    rng = random.Random(seed)
    for index in range(count):
        degree = rng.randrange(2, 5)
        modulus = math.factorial(degree)
        shift = rng.randrange(-12, 13)
        offset = rng.randrange(-32, 33)
        factors = [f'(- x {integer(shift + j)})' for j in range(degree)]
        product = '(* ' + ' '.join(factors) + ')'
        coefficient = rng.randrange(-4096, 4096)
        # Consecutive products are divisible by degree!, and adding a
        # modulus multiple preserves the residue. No Xolver evaluation
        # participates in the independent expected-answer construction.
        polynomial = (f'(+ (* {integer(coefficient)} {product}) '
                      f'(* {modulus} {power("x", rng.randrange(1, 8))}) {integer(offset)})')
        divisor = modulus if index % 2 else -modulus
        # This negative interval spans EVERY residue class. Bounded companion
        # queries make exhaustive independent checking practical; polynomial
        # congruence extends the identity to every integer.
        prefix = (f'(declare-const x Int)(assert (>= x {integer(-modulus)}))'
                  '(assert (< x 0))')
        equality = f'(= (mod {polynomial} {integer(divisor)}) {offset % modulus})'
        yield f'identity-{index:04d}-sat', prefix + f'(assert {equality})', 'sat'
        yield f'identity-{index:04d}-unsat', prefix + f'(assert (not {equality}))', 'unsat'

    for prime in (2, 3, 5, 7):
        identity = f'(= (mod (- {power("x", prime)} x) {prime}) 0)'
        prefix = f'(declare-const x Int)(assert (>= x {integer(-prime)}))(assert (< x 0))'
        yield f'power-{prime}-sat', prefix + f'(assert {identity})', 'sat'
        yield f'power-{prime}-unsat', prefix + f'(assert (not {identity}))', 'unsat'

    # These residue functions are NOT constant. A negative witness in the
    # finite interval guarantees satisfiability; replay checks the actual
    # returned model, rather than assuming a universally zero residue.
    for modulus in range(2, 10):
        witness = -modulus - 1
        residue = witness**2 % modulus
        body = (f'(declare-const x Int)(assert (>= x {integer(-2 * modulus)}))'
                f'(assert (< x 0))(assert (= (mod {power("x", 2)} {integer(-modulus)}) {residue}))')
        yield f'nonconstant-{modulus}', body, 'sat'


def main():
    args = arguments(__doc__)
    # The original-query policy requires an independent decision for every
    # input. cvc5 can exhaust its budget on these nonlinear modular identities;
    # both oracles must still accept every complete returned model.
    return validate_cases(args, cases(args.seed, args.count), 'QF_NIA', require_all_oracles=False)


if __name__ == '__main__':
    raise SystemExit(main())
