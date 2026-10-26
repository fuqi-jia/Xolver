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


if __name__ == '__main__':
    unittest.main()
