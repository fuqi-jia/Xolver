"""Isolating intervals identify the exact exported algebraic model value."""
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/fuzz'))
from algebraic_model import indexed_root_interval, isolates_unique_real_root, root_object_polynomial
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

    def test_indexed_roots_are_in_increasing_one_based_order(self):
        for coefficients, expected in [([-2, 0, 1], [-2, 2]),
                                       ([4, 0, -5, 0, 1], [-2, -1, 1, 2])]:
            for index, root in enumerate(expected, 1):
                low, high = indexed_root_interval(coefficients, index)
                self.assertTrue(isolates_unique_real_root(coefficients, low, high))
                if len(coefficients) == 3:
                    self.assertTrue(high <= 0 if root < 0 else low >= 0)
                else:
                    self.assertLess(low, root)
                    self.assertLess(root, high)

    def test_indexed_rational_and_repeated_roots_remain_inside_open_intervals(self):
        for coefficients, roots in [([0, -1, 0, 1], [-1, 0, 1]),
                                    ([2, -3, 0, 1], [-2, 1])]:
            for index, root in enumerate(roots, 1):
                low, high = indexed_root_interval(coefficients, index)
                self.assertLess(low, root)
                self.assertLess(root, high)
                self.assertTrue(isolates_unique_real_root(coefficients, low, high))
            with self.assertRaisesRegex(ValueError, 'exceeds'):
                indexed_root_interval(coefficients, len(roots) + 1)

    def test_index_and_isolation_allocation_errors_reject_the_witness(self):
        for index in [0, -1, Fraction(1, 2), 3]:
            with self.assertRaises(ValueError):
                indexed_root_interval([-2, 0, 1], index)
        with self.assertRaisesRegex(ValueError, 'allocation exhausted'):
            indexed_root_interval([0, -Fraction(1, 1024), 1], 1, max_refinements=1)

    def test_indexed_polynomials_normalize_exact_rational_coefficients(self):
        for expression, expected in [('(- (^ x 2) (/ 1 2))', [-1, 0, 2]),
                                     ('(- 2 (* 2 (^ x 2)))', [-1, 0, 1]),
                                     ('(* (- x 1) (- x 1) (+ x 2))', [2, -3, 0, 1])]:
            self.assertEqual(root_object_polynomial(parse(expression)[0]), tuple(expected))

    def test_indexed_polynomials_reject_unbound_symbols_and_nonpolynomial_terms(self):
        for expression in ['(+ x y)', '(/ 1 x)', '(^ x (- 1))', '(^ x (/ 1 2))',
                           '(^ x 1000000)', '(* x (- x x))']:
            with self.assertRaises(ValueError):
                root_object_polynomial(parse(expression)[0])

    def test_z3_root_objects_replay_without_capturing_original_x(self):
        prefix = '(set-logic QF_NRA)(declare-const x Real)(assert (> x 0))'
        root = '(root-obj (+ (^ x 2) (- 2)) 2)'
        pinned = replay(prefix, 'sat (model (define-fun x () Real '+root+'))')
        self.assertIn('(define-fun x () Real __xolver_algebraic_witness_0)', pinned)
        self.assertIn('(assert (> x 0))', pinned)
        self.assertNotIn('root-obj', pinned)
        self.assertNotIn('(^ x', pinned)
        parse(pinned)

    def test_real_polynomial_logic_is_preserved_for_independent_replay(self):
        root = '(root-obj (- (^ x 2) 2) 2)'
        for logic in ['QF_NRA', 'NRA', 'ALL']:
            prefix = '(set-logic '+logic+')(declare-const x Real)(assert (> x 0))'
            pinned = replay(prefix, 'sat (model (define-fun x () Real '+root+'))')
            self.assertIn('(set-logic '+logic+')', pinned)
            self.assertEqual(pinned.count('(set-logic '), 1)

    def test_nested_and_reused_indexed_roots_preserve_the_selected_value(self):
        root = '(root-obj (+ (^ x 4) (* (- 5) (^ x 2)) 4) 3)'
        output = 'sat (model (define-fun a () Real (+ 1 '+root+'))(define-fun b () Real '+root+'))'
        pinned = replay('(declare-const a Real)(declare-const b Real)(assert (= a (+ b 1)))', output)
        self.assertEqual(pinned.count('(declare-const __xolver_algebraic_witness_'), 1)
        self.assertIn('(define-fun a () Real (+ 1 __xolver_algebraic_witness_0))', pinned)
        self.assertIn('(assert (= a (+ b 1)))', pinned)

    def test_malformed_or_colliding_root_objects_are_rejected(self):
        for root in ['(root-obj (+ (^ x 2) (- 2)) 0)',
                     '(root-obj (+ (^ x 2) (- 2)) 3)',
                     '(root-obj (+ (^ x 2) (- 2)) (/ 1 2))',
                     '(root-obj (+ (^ x 2) (- 2)))']:
            with self.assertRaises(ValueError):
                replay('(declare-const a Real)', 'sat (model (define-fun a () Real '+root+'))')
        with self.assertRaisesRegex(ValueError, 'collides'):
            replay('(declare-const |root-obj| Real)(declare-const a Real)',
                   'sat (model (define-fun root-obj () Real 0)'
                   '(define-fun a () Real (root-obj (- (^ x 2) 2) 2)))')


if __name__ == '__main__':
    unittest.main()
