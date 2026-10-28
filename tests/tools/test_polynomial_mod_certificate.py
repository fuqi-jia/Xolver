import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/soundness'))
from polynomial_mod_certificate import Unsupported, produce, verify


def query(body, declarations='(declare-const x Int)'):
    return ('(set-logic QF_NIA)' + declarations + '(assert ' + body + ')(check-sat)').encode()


class PolynomialModCertificateTests(unittest.TestCase):
    def checked(self, data):
        certificate = produce(data)
        self.assertEqual(verify(data, certificate)['status'], 'checked-unsat')
        return certificate

    def test_source_polynomial_with_shared_let_and_conjunction(self):
        data = query('(let ((s (* x x))) (and (not (= (mod (+ (* 10 x x x x x x) '
                     '(* 6 x x x x x) (* 7 x x x x) s) 12) 0)) (> x 1000000)))')
        certificate = self.checked(data)
        self.assertEqual(certificate['coefficients'], [0, 0, 1, 0, 7, 6, 10])
        self.assertEqual(certificate['residues'], [0] * 12)

    def test_negative_divisor_zero_identity_and_reversed_equality(self):
        self.checked(query('(not (= 0 (mod (- (* x x) x) (- 2))))'))

    def test_reject_modified_source_and_certificate(self):
        data = query('(not (= (mod (- (* x x) x) 2) 0))')
        certificate = self.checked(data)
        with self.assertRaises(Unsupported):
            verify(data + b'\n', certificate)
        for key, bad in [('residues', [0]), ('residues', [0, 1]),
                         ('coefficients', [0, 1]), ('path', [7]), ('modulus', 3)]:
            corrupted = copy.deepcopy(certificate)
            corrupted[key] = bad
            with self.subTest(key=key, bad=bad), self.assertRaises(Unsupported):
                verify(data, corrupted)

    def test_no_contradiction_under_or_implication_or_double_negation(self):
        false_literal = '(not (= (mod (- (* x x) x) 2) 0))'
        for body in ['(or true ' + false_literal + ')',
                     '(=> false ' + false_literal + ')', '(not ' + false_literal + ')']:
            with self.subTest(body=body), self.assertRaises(Unsupported):
                produce(query(body))

    def test_reject_zero_divisor_and_nonconstant_residue(self):
        for body in ['(not (= (mod (* x x) 2) 0))',
                     '(not (= (mod (- (* x x) x) 0) 0))',
                     '(not (= (mod (- (* x x) x) x) 0))']:
            with self.subTest(body=body), self.assertRaises(Unsupported):
                produce(query(body))

    def test_integer_domain_and_single_query_are_required(self):
        literal = '(not (= (mod (- (* x x) x) 2) 0))'
        for data in [query(literal, '(declare-const x Real)'),
                     query(literal).replace(b'(check-sat)', b'(pop 1)(check-sat)'),
                     query(literal) + b'(check-sat)',
                     b'(assert ' + literal.encode() + b')(declare-const x Int)(check-sat)']:
            with self.subTest(data=data), self.assertRaises(Unsupported):
                produce(data)

    def test_simultaneous_let_does_not_capture_outer_variables(self):
        # The RHS of the second binding uses the original x, so the query is
        # satisfiable for x=1. Sequential/capturing expansion would prove false.
        data = query('(let ((x 0) (s x)) (not (= (mod s 2) 0)))')
        with self.assertRaises(Unsupported):
            produce(data)

    def test_quoted_numeric_identifier_does_not_capture_numeral(self):
        self.checked(query('(let ((|0| x)) (not (= (mod (* 0 |0|) 2) 0)))'))
        data = query('(let ((|0| 0)) (not (= (mod (+ 1 |0|) 2) 0)))')
        with self.assertRaises(Unsupported):
            produce(data)

    def test_quoted_and_unquoted_names_denote_the_same_integer(self):
        self.checked(query('(not (= (mod (- (* |x| x) x) 2) 0))'))

    def test_unbounded_nonzero_disequality_is_not_a_residue_condition(self):
        # x != 0 is satisfiable even if x is zero modulo 2. No bounded-variable
        # or filename assumption may turn it into an UNSAT certificate.
        with self.assertRaises(Unsupported):
            produce(query('(and (not (= x 0)) (= (mod x 2) 0))'))


if __name__ == '__main__':
    unittest.main()
