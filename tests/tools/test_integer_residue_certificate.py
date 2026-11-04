"""Residue certificates must refute every possible integer residue class."""
import hashlib
import sys
from pathlib import Path
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/proof'))
from check_integer_residue_certificate import Unsupported, verify_certificate


def certificate(source, modulus):
    return dict(version=1, kind='integer-residue-exhaustion', modulus=modulus,
                input_sha256=hashlib.sha256(source.encode()).hexdigest())


class IntegerResidueCertificateTests(unittest.TestCase):
    def test_complete_refutations(self):
        cases = [
            ('(declare-const x Int)(assert (= (* x x) 2))(check-sat)', 4),
            ('(declare-const x Int)(assert (= (mod (* x (- x 1)) 2) 1))(check-sat)', 2),
            ('(declare-const x Int)(assert (= (mod x 3) 1))'
             '(assert (= (mod x 3) 2))(check-sat)', 3),
            ('(declare-const x Int)(assert (not (= (mod (+ (* 2 x) 1) 2) 1)))(check-sat)', 2),
            ('(declare-const x Int)(assert (let ((a x) (x (+ x 1)))'
             ' (not (= (mod (- x a) 2) 1))))(check-sat)', 2),
            ('(assert false)(check-sat)', 2),
            ('(assert false)\r\n(check-sat)\r\n', 2),
        ]
        for source, modulus in cases:
            with self.subTest(source=source):
                result = verify_certificate(source, certificate(source, modulus))
                self.assertEqual(result['status'], 'verified')
                self.assertEqual(result['valuations'], modulus ** result['variables'])

    def test_possible_residues_and_unknown_equalities_do_not_refute(self):
        cases = [
            '(declare-const x Int)(assert (= (* x x) 4))(check-sat)',
            '(declare-const x Int)(assert (distinct x 0))(check-sat)',
            '(declare-const x Int)(assert (not (= x 0)))(check-sat)',
            '(declare-const x Int)(assert (< x 0))(check-sat)',
            '(declare-const x Int)(assert (= (mod x 2) 0))(check-sat)',
            '(assert true)(check-sat)',
            '(declare-const x Int)(assert (let ((x 1) (y x)) (= y 0)))(check-sat)',
            '(declare-const |0| Int)(assert (= |0| 1))'
            '(assert (= (+ 0 1) 1))(check-sat)',
        ]
        for source in cases:
            for modulus in [2, 3, 4]:
                with self.subTest(source=source, modulus=modulus):
                    self.assertEqual(verify_certificate(source, certificate(source, modulus))['status'],
                                     'not_verified')
        # Equal modulo two is insufficient to prove equality over integers.
        source = '(declare-const x Int)(assert (= (* x x) 2))(check-sat)'
        self.assertEqual(verify_certificate(source, certificate(source, 2))['status'], 'not_verified')

    def test_invalid_or_unsupported_claims_fail_closed(self):
        sources = [
            '(declare-const x Real)(assert (= x 0.5))(check-sat)',
            '(declare-const x Int)(assert (= (div x 2) 0))(check-sat)',
            '(declare-const x Int)(assert (= (mod x 0) 0))(check-sat)',
            '(declare-const x Int)(assert (= (mod x (- 2)) 0))(check-sat)',
            '(declare-const x Int)(assert (= (mod x x) 0))(check-sat)',
            '(assert false)(check-sat)(check-sat)',
            '(check-sat)(assert false)',
            '(exit)(assert false)(check-sat)',
            '(assert false)(check-sat x)',
            '(declare-const x Int)(declare-const x Int)(assert false)(check-sat)',
        ]
        for source in sources:
            with self.subTest(source=source):
                with self.assertRaises((Unsupported, ValueError)):
                    verify_certificate(source, certificate(source, 2))
        source = '(assert false)(check-sat)'
        invalid = certificate(source, 2)
        invalid['input_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'digest'):
            verify_certificate(source, invalid)
        for field, value in [('modulus', 1), ('modulus', 2.0), ('version', 2)]:
            invalid = certificate(source, 2); invalid[field] = value
            with self.assertRaises(ValueError):
                verify_certificate(source, invalid)

    def test_resource_exhaustion_does_not_accept_a_partial_proof(self):
        source = '(assert false)(check-sat)'
        large = '(declare-const x Int)(assert (= x 0))(check-sat)'
        result = verify_certificate(large, certificate(large, 10 ** 80))
        self.assertEqual(result, dict(status='not_verified', valuations=1))
        with self.assertRaises(TimeoutError):
            verify_certificate(source, certificate(source, 2), time.monotonic() - 1)


if __name__ == '__main__':
    unittest.main()
