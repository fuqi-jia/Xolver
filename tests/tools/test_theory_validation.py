"""Check that external-model validation cannot silently omit interpretations."""
import sys
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/fuzz'))
import fuzz_theory_applications as theory
import fuzz_linear_arithmetic as linear


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

    def test_resource_limited_oracles_cannot_hide_wrong_answers_or_bad_models(self):
        scenarios = [
            # One independent original-query decision is sufficient only under
            # the explicit affine policy. Model replay still needs both oracles.
            ('sat', 'timeout', 'sat', 'sat', False, False),
            ('sat', 'timeout', 'sat', 'sat', True, True),
            ('sat', 'timeout', 'unknown', 'sat', False, True),
            ('sat', 'unsat', 'sat', 'sat', False, True),
            ('sat', 'error', 'sat', 'sat', False, True),
            ('unknown', 'sat', 'sat', 'sat', False, True),
            ('sat', 'timeout', 'sat', 'timeout', False, True),
            ('sat', 'timeout', 'sat', 'unsat', False, True),
        ]
        for xolver, z3, cvc5, replay, strict, failure in scenarios:
            with self.subTest(scenario=(xolver, z3, cvc5, replay, strict)), TemporaryDirectory() as tmp:
                root = Path(tmp)
                for engine in ('xolver', 'z3', 'cvc5'):
                    (root / engine).write_text('test binary placeholder')
                args = SimpleNamespace(solver=root / 'xolver', z3=root / 'z3', cvc5=root / 'cvc5',
                                       output=root / 'out', timeout=5, seed=0)

                def invoke(command, source, timeout):
                    engine = Path(command[0]).name
                    verdict = replay if source.stem.endswith('-replay') else {
                        'xolver': xolver, 'z3': z3, 'cvc5': cvc5}[engine]
                    return dict(verdict=verdict, stdout='sat\n((define-fun x () Int 0))')

                with patch.object(linear, 'invoke', side_effect=invoke), \
                        patch.object(linear.subprocess, 'run', return_value=SimpleNamespace(stdout='test', stderr='')), \
                        patch.dict(linear.os.environ, {'EOS_METRICS_FILE': str(root / 'metrics.json')}), \
                        patch('builtins.print'):
                    result = linear.validate_cases(args, [('case', '(declare-const x Int)', 'sat')],
                                                   'QF_LIA', require_all_oracles=strict)
                self.assertEqual(bool(result), failure)
                summary = json.loads((args.output / 'summary.json').read_text())
                if not strict:
                    self.assertIn('oracle_limits', summary)
                if not failure:
                    self.assertEqual(summary['oracle_confirmed'], 1)
                    self.assertEqual(summary['oracle_limits'],
                                     [dict(case='case', engine='z3', actual='timeout')])


if __name__ == '__main__':
    unittest.main()
