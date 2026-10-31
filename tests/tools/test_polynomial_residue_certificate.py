#!/usr/bin/env python3
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/soundness'))
from polynomial_residue_certificate import Unsupported, produce, verify

SOURCE = b'''(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)(declare-const z Int)(declare-const w Int)
(assert (= (+ (* x x) (* y y)) (* 3 z)))
(assert (= (+ x y) (+ 1 (* 3 w))))(check-sat)'''


class ResidueCertificateTests(unittest.TestCase):
    def test_original_conjunction_has_complete_independent_cover(self):
        certificate = produce(SOURCE)
        result = verify(SOURCE, certificate)
        self.assertEqual(result['result'], 'unsat')
        self.assertEqual(result['checked_residue_classes'], 81)

    def test_incomplete_duplicate_and_false_rejections_fail(self):
        original = produce(SOURCE)
        for damage in ('missing', 'duplicate', 'invalid-rejection', 'invalid-premise', 'wrong-hash'):
            certificate = copy.deepcopy(original)
            if damage == 'missing':
                certificate['cover'].pop()
            elif damage == 'duplicate':
                certificate['cover'][1] = certificate['cover'][0]
            elif damage == 'invalid-rejection':
                # At the all-zero tuple, the first equality is satisfied.
                certificate['cover'][0]['violated_equality'] = 0
            elif damage == 'invalid-premise':
                certificate['equalities'][0]['path'] = [42]
            else:
                certificate['input_sha256'] = '0'*64
            with self.subTest(damage=damage), self.assertRaises(Unsupported):
                verify(SOURCE, certificate)

    def test_real_declarations_and_stateful_queries_are_rejected(self):
        for source in (SOURCE.replace(b'Int', b'Real'), SOURCE+b'(check-sat)',
                       SOURCE.replace(b'(check-sat)', b'(push 1)(check-sat)'),
                       b'(set-logic QF_NIA)(assert (= x 0))(declare-const x Int)(assert (= x 1))(check-sat)'):
            with self.assertRaises(Unsupported):
                produce(source)

    def test_satisfiable_and_disjunctive_inputs_cannot_be_certified(self):
        for source in (b'(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 1))(check-sat)',
                       b'(set-logic QF_NIA)(declare-const x Int)(assert (or (= (* x x) 2) (= x 0)))(check-sat)'):
            with self.assertRaises(Unsupported):
                produce(source)

    def test_positive_conjunctions_and_simultaneous_let_bindings(self):
        source = b'''(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)
        (assert (let ((a x) (b y)) (and (= (* a a) 2) (= b 0))))(check-sat)'''
        certificate = produce(source, 4)
        self.assertEqual(verify(source, certificate)['checked_residue_classes'], 16)
        with self.assertRaises(Unsupported):
            produce(source, 1)


if __name__ == '__main__':
    unittest.main()
