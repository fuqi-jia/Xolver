"""Keep independent model replay usable for deeply nested SMT-LIB inputs."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/fuzz'))
from fuzz_theory_applications import emit, parse, replay


class ModelReplaySerialization(unittest.TestCase):
    def test_deep_assertion(self):
        source = '(assert ' + '(not ' * 5000 + 'true' + ')' * 5000 + ')'
        self.assertEqual(emit(parse(source)[0]), source)

    def test_quoted_symbols_and_strings(self):
        source = '(assert (= |name with spaces| "text ""quoted"""))'
        self.assertEqual(emit(parse(source)[0]), source)

    def test_invalid_node(self):
        with self.assertRaises(ValueError):
            emit(['unparsed text'])

    def test_model_may_drop_optional_symbol_quoting(self):
        source = '(set-logic QF_LIA)(declare-const |x| Int)(assert (= |x| 3))'
        output = 'sat\n(model (define-fun x () Int 3))'
        pinned = replay(source, output)
        self.assertIn('(define-fun x () Int 3)', pinned)
        self.assertNotIn('declare-const', pinned)
        self.assertIn('(assert (= |x| 3))', pinned)

    def test_quoted_duplicate_interpretations_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate model definition'):
            replay('(declare-const x Int)',
                   'sat (model (define-fun x () Int 3)(define-fun |x| () Int 3))')

    def test_unused_model_universe_can_be_projected_out(self):
        source = '(set-logic QF_LIA)(declare-const x Int)(assert (= x 3))'
        output = '''sat (model
            (declare-fun U!val!0 () U)
            (forall ((u U)) (= u U!val!0))
            (define-fun x () Int 3))'''
        pinned = replay(source, output)
        self.assertIn('(define-fun x () Int 3)', pinned)
        self.assertIn('(assert (= x 3))', pinned)
        self.assertNotIn('U!val!0', pinned)
        self.assertNotIn('forall', pinned)

    def test_referenced_universe_element_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'uses auxiliary universe element'):
            replay('(declare-sort U 0)(declare-const x U)', '''sat (model
                (declare-fun U!val!0 () U)
                (define-fun x () U U!val!0))''')

    def test_universe_constraint_on_original_symbol_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'references original symbol'):
            replay('(declare-const x Int)', '''sat (model
                (forall ((u Int)) (= x u))
                (define-fun x () Int 3))''')

    def test_auxiliary_declaration_cannot_shadow_original_symbol(self):
        with self.assertRaisesRegex(ValueError, 'shadows original symbol'):
            replay('(declare-const x Int)',
                   'sat (model (declare-fun |x| () Int))')

    def test_auxiliary_declaration_cannot_duplicate_definition(self):
        with self.assertRaisesRegex(ValueError, 'duplicate model definition'):
            replay('(declare-const x Int)', '''sat (model
                (declare-fun a () Int)(define-fun |a| () Int 0)
                (define-fun x () Int 3))''')

    def test_unsupported_model_command_is_still_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unsupported model binding'):
            replay('(declare-const x Int)', '''sat (model
                (assert true)(define-fun x () Int 3))''')


if __name__ == '__main__':
    unittest.main()
