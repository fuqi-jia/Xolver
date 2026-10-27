"""Isolating intervals identify the exact exported algebraic model value."""
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/fuzz'))
from algebraic_model import isolates_unique_real_root
from fuzz_theory_applications import parse, replay

ROOT = '(root-of-with-interval (coeffs (- 2) 0 1) 1.0 2.0)'


class AlgebraicModelReplay(unittest.TestCase):
    def test_signed_unique_roots(self):
        for low, high in [(1, 2), (-2, -1)]:
            self.assertTrue(isolates_unique_real_root([-2, 0, 1], low, high))

    def test_zero_or_multiple_roots_are_rejected(self):
        for low, high in [(-2, 2), (2, 3), (2, 1), (1, 1)]:
            self.assertFalse(isolates_unique_real_root([-2, 0, 1], low, high))
        self.assertFalse(isolates_unique_real_root([0, 0], -1, 1))
        self.assertFalse(isolates_unique_real_root([1], -1, 1))

    def test_boundary_root_is_rejected(self):
        self.assertFalse(isolates_unique_real_root([-1, 1], 1, 2))

    def test_repeated_root_is_one_distinct_value(self):
        self.assertTrue(isolates_unique_real_root([1, -2, 1], 0, 2))
        self.assertFalse(isolates_unique_real_root([0, 0, -1, 0, 1], -2, 2))

    def test_rational_isolating_interval(self):
        self.assertTrue(isolates_unique_real_root([-2, -12, 207], Fraction(7, 69), Fraction(4, 23)))

    def test_nested_model_expression_preserves_original_formula(self):
        prefix = '(set-logic QF_LRA)(declare-const x Real)(assert (> x 2))'
        output = 'sat (model (define-fun x () Real (+ 1 ' + ROOT + ')))'
        pinned = replay(prefix, output)
        self.assertIn('(set-logic ALL)', pinned)
        self.assertIn('(define-fun x () Real (+ 1 __xolver_algebraic_witness_0))', pinned)
        self.assertIn('(assert (> x 2))', pinned)
        self.assertIn('(assert (and (< 1 __xolver_algebraic_witness_0)', pinned)
        self.assertNotIn('root-of-with-interval', pinned)
        parse(pinned)

    def test_fresh_witness_does_not_shadow_quoted_source_symbol(self):
        prefix = '(declare-const |__xolver_algebraic_witness_0| Real)(declare-const x Real)'
        output = 'sat (model (define-fun __xolver_algebraic_witness_0 () Real 3)(define-fun x () Real '+ROOT+'))'
        pinned = replay(prefix, output)
        self.assertIn('(declare-const __xolver_algebraic_witness_1 Real)', pinned)
        self.assertIn('(define-fun __xolver_algebraic_witness_0 () Real 3)', pinned)

    def test_bad_isolation_is_rejected_before_oracle(self):
        with self.assertRaisesRegex(ValueError, 'exactly one real root'):
            replay('(declare-const x Real)', 'sat (model (define-fun x () Real '+ROOT.replace('1.0 2.0', '(- 2.0) 2.0')+'))')

    def test_non_integer_defining_coefficient_is_rejected(self):
        root = ROOT.replace('(coeffs (- 2) 0 1)', '(coeffs (- 2) 0 (/ 1 2))')
        with self.assertRaisesRegex(ValueError, 'coefficients must be integers'):
            replay('(declare-const x Real)', 'sat (model (define-fun x () Real '+root+'))')

    def test_constructor_name_collision_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'collides'):
            replay('(declare-const coeffs Real)(declare-const x Real)',
                   'sat (model (define-fun coeffs () Real 0)(define-fun x () Real '+ROOT+'))')

    def test_reused_root_has_one_witness(self):
        pinned = replay('(declare-const x Real)(declare-const y Real)',
                        'sat (model (define-fun x () Real '+ROOT+')(define-fun y () Real '+ROOT+'))')
        self.assertEqual(pinned.count('(declare-const __xolver_algebraic_witness_'), 1)


if __name__ == '__main__':
    unittest.main()
