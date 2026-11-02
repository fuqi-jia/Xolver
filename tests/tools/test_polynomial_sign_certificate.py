import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/proof'))
from check_polynomial_sign_certificate import Checker


class PolynomialSignCertificateTests(unittest.TestCase):
    source = '''(set-logic QF_NRA)
(declare-const d Real) (declare-const b Real)
(assert (> d 0)) (assert (> b 0))
(assert (= (+ (* d d b) (* d b b) (* d d) (* b b) d b (* (- 5) d b)) 0))
(check-sat)'''

    def certificate(self, source=None):
        return dict(input_sha256=hashlib.sha256((source or self.source).encode()).hexdigest(),
                    multipliers=[dict(premise=2, factor='1')],
                    positive_expression='(+ (^ (- d b) 2) (* d (^ (- b 1) 2)) (* b (^ (- d 1) 2)) (* d b))')

    def test_exact_identity_with_nonnegative_squares(self):
        self.assertTrue(Checker(self.source, self.certificate()).check()['checked'])

    def test_changed_coefficient_is_rejected(self):
        certificate = self.certificate()
        certificate['multipliers'][0]['factor'] = '2'
        with self.assertRaisesRegex(ValueError, 'identity mismatch'):
            Checker(self.source, certificate).check()

    def test_zero_identity_is_not_a_strict_contradiction(self):
        certificate = self.certificate()
        certificate['multipliers'][0]['factor'] = '0'
        certificate['positive_expression'] = '0'
        with self.assertRaisesRegex(ValueError, 'strictly positive'):
            Checker(self.source, certificate).check()

    def test_missing_sign_premise_is_rejected(self):
        source = self.source.replace('(> d 0)', '(>= d 0)')
        with self.assertRaisesRegex(ValueError, 'strictly positive'):
            Checker(source, self.certificate(source)).check()

    def test_conditional_sign_premise_is_not_unconditional(self):
        source = self.source.replace('(> d 0)', '(or (> d 0) (< d 0))')
        with self.assertRaisesRegex(ValueError, 'strictly positive'):
            Checker(source, self.certificate(source)).check()

    def test_input_hash_and_premise_indices_are_checked(self):
        with self.assertRaisesRegex(ValueError, 'input hash'):
            Checker(self.source + '\n', self.certificate())
        certificate = self.certificate()
        certificate['multipliers'][0]['premise'] = -1
        with self.assertRaisesRegex(ValueError, 'premise index'):
            Checker(self.source, certificate).check()

    def test_certificate_definitions_cannot_shadow_input(self):
        certificate = self.certificate()
        certificate['definitions'] = {'d': '1'}
        with self.assertRaisesRegex(ValueError, 'shadows'):
            Checker(self.source, certificate)

    def test_macros_cannot_reinterpret_input_constants(self):
        certificate = self.certificate()
        certificate['definitions'] = {'0': '1'}
        with self.assertRaisesRegex(ValueError, 'shadows'):
            Checker(self.source, certificate)

    def test_scope_changes_and_multiple_queries_are_rejected(self):
        for suffix in ['(push 1)', '(pop 1)', '(reset-assertions)',
                       '(assert (= d 0))', '(check-sat)']:
            source = self.source + suffix
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                Checker(source, self.certificate(source)).check()

    def test_rational_coefficients_and_macro_expansion_are_exact(self):
        source = '(declare-const x Int) (assert (= (+ (* (/ 1 3) x x) (/ 2 7)) 0))'
        certificate = dict(input_sha256=hashlib.sha256(source.encode()).hexdigest(),
                           definitions={'square': '(^ x 2)'},
                           multipliers=[dict(premise=0, factor='21')],
                           positive_expression='(+ (* 7 square) 6)')
        self.assertTrue(Checker(source, certificate).check()['checked'])


if __name__ == '__main__':
    unittest.main()
