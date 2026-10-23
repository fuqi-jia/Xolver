"""Check that external-model validation cannot silently omit interpretations."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/fuzz'))
import fuzz_theory_applications as theory


class TheoryValidation(unittest.TestCase):
    def test_generated_queries_are_balanced_and_unique(self):
        cases = list(theory.cases(20261023, 32))
        self.assertEqual(len(cases), len({c[0] for c in cases}))
        self.assertGreater(len(cases), 200)
        for name, source, expected in cases:
            with self.subTest(name=name):
                self.assertTrue(theory.parse(source))
                self.assertIsInstance(expected, bool)

    def test_replay_preserves_unicode_escapes_and_quoted_symbols(self):
        prefix = '(declare-const |s x| String)(assert (= |s x| "a""\\u{1f600}"))'
        model = 'sat\n((define-fun |s x| () String "a""\\u{1f600}"))'
        result = theory.replay(prefix, model)
        self.assertIn('(define-fun |s x| () String "a""\\u{1f600}")', result)
        self.assertIn('(assert (= |s x| "a""\\u{1f600}"))', result)
        self.assertNotIn('declare-const', result)

    def test_missing_interpretations_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing interpretation'):
            theory.replay('(declare-const x Bool)', 'sat\n()')

    def test_wrong_signatures_are_rejected(self):
        for model in ['sat\n((define-fun f () Bool true))',
                      'sat\n((define-fun f ((x Int)) Bool true))',
                      'sat\n((define-fun f ((x Bool)) Int 0))']:
            with self.subTest(model=model), self.assertRaisesRegex(ValueError, 'signature mismatch'):
                theory.replay('(declare-fun f (Bool) Bool)', model)

    def test_extra_error_output_is_rejected(self):
        with self.assertRaises(ValueError):
            theory.replay('', 'sat\n()\n(error "bad model")')

    def test_function_interpretations_replace_declarations(self):
        result = theory.replay('(declare-fun f (Bool) Bool)(assert (f true))',
                               'sat\n(model (define-fun f ((x Bool)) Bool x))')
        self.assertIn('(define-fun f ((x Bool)) Bool x)', result)
        self.assertNotIn('declare-fun', result)


if __name__ == '__main__':
    unittest.main()
