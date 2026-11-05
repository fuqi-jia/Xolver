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

    def test_referenced_universe_is_distinct_closed_and_pins_every_interpretation(self):
        source = '''(set-logic QF_UF)(declare-sort U 0)
            (declare-const x U)(declare-const y U)(assert (distinct x y))'''
        model = '''sat (model
            (declare-fun U!val!0 () U)(declare-fun U!val!1 () U)
            (define-fun x () U U!val!0)(define-fun y () U U!val!1))'''
        pinned = replay(source, model)
        self.assertIn('(set-logic ALL)', pinned)
        self.assertIn('(declare-datatype U ((U!val!0) (U!val!1)))', pinned)
        self.assertNotIn('(declare-fun U!val!0 () U)', pinned)
        self.assertIn('(define-fun x () U U!val!0)', pinned)
        self.assertIn('(define-fun y () U U!val!1)', pinned)
        self.assertEqual(pinned.count('(assert (distinct x y))'), 1)
        self.assertLess(pinned.index('(declare-datatype U'),
                        pinned.index('(define-fun x'))

    def test_provided_universe_quantifier_can_shadow_an_original_variable(self):
        pinned = replay('(declare-sort U 0)(declare-const x U)', '''sat (model
            (declare-fun U!val!0 () U)
            (forall ((x U)) (= x U!val!0))
            (define-fun x () U U!val!0))''')
        self.assertIn('(assert (forall ((x U)) (= x U!val!0)))', pinned)

    def test_model_parameter_does_not_activate_a_shadowed_domain_value(self):
        pinned = replay('(declare-sort U 0)(declare-fun f (U) U)', '''sat (model
            (declare-fun U!val!0 () U)
            (define-fun f ((U!val!0 U)) U U!val!0))''')
        self.assertNotIn('(declare-fun U!val!0 () U)', pinned)
        self.assertIn('(define-fun f ((U!val!0 U)) U U!val!0)', pinned)

    def test_numeric_literal_does_not_activate_a_quoted_numeric_value(self):
        pinned = replay('(declare-sort U 0)(declare-const x Int)', '''sat (model
            (declare-fun |0| () U)(define-fun x () Int 0))''')
        self.assertNotIn('(declare-fun |0| () U)', pinned)
        self.assertNotIn('forall', pinned)

    def test_aliases_use_one_underlying_domain(self):
        pinned = replay('''(declare-sort U 0)(define-sort V () U)
            (declare-const x V)(declare-const y U)''', '''sat (model
            (declare-fun u0 () V)(declare-fun u1 () U)
            (define-fun x () V u0)(define-fun y () U u1))''')
        self.assertIn('(declare-datatype U ((u0) (u1)))', pinned)
        self.assertIn('(define-sort V () U)', pinned)
        self.assertEqual(pinned.count('(declare-datatype U'), 1)

    def test_numerical_or_undeclared_auxiliary_domains_remain_unsupported(self):
        for source, sort in [('(declare-const x Int)', 'Int'),
                             ('(declare-sort U 0)(declare-const x U)', 'Other')]:
            with self.subTest(sort=sort), self.assertRaisesRegex(ValueError, 'auxiliary model domain'):
                replay(source, 'sat (model (declare-fun v () ' + sort + ')'
                       '(define-fun x () ' + sort + ' v))')

    def test_incomplete_or_nonmembership_universe_constraints_are_rejected(self):
        for body in ['(= x u0)', '(= x x)', '(not (= x u0))']:
            with self.subTest(body=body), self.assertRaises(ValueError):
                replay('(declare-sort U 0)(declare-const y U)', '''sat (model
                    (declare-fun u0 () U)(declare-fun u1 () U)
                    (forall ((x U)) ''' + body + ''')
                    (define-fun y () U u0))''')

    def test_source_defined_function_interpretations_are_checked(self):
        source = '(define-fun f ((p Int)) Int (+ p 1))(assert (= (f 0) 1))'
        pinned = replay(source, 'sat (model (define-fun f ((f Int)) Int 0))')
        self.assertIn('(define-fun f ((p Int)) Int (+ p 1))', pinned)
        self.assertIn('(assert (= (f 0) 1))', pinned)
        self.assertIn('(assert (forall ((f Int))', pinned)
        self.assertNotIn('(define-fun f ((f Int)) Int 0)', pinned)

    def test_model_universe_binder_avoids_domain_value_capture(self):
        pinned = replay('(declare-sort U 0)(declare-const x U)', '''sat (model
            (declare-fun __xolver_model_domain () U)
            (define-fun x () U __xolver_model_domain))''')
        self.assertIn('(declare-datatype U ((__xolver_model_domain)))', pinned)
        self.assertIn('(define-fun x () U __xolver_model_domain)', pinned)
        self.assertNotIn('forall', pinned)

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
