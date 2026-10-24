import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import Unsupported, binders, export_goals, parse


class QcpAdapterTests(unittest.TestCase):
    def test_requires_declared_types_and_consumes_whole_expression(self):
        for expression in ('mystery + 1 = 2', 'f (x) = 1', 'x = 0 trailing', 'x + True = 2'):
            with self.subTest(expression=expression), self.assertRaises(Unsupported):
                parse(expression, {'x': 'Int'})
        with self.assertRaises(Unsupported):
            binders('forall (x : list Z), True')
        with self.assertRaises(Unsupported):
            binders('forall (x : Z) (x : Z), x = x')

    def test_negation_and_implication_precedence(self):
        result = parse('~ x = 0 /\\ x <= 4 -> x <> 9', {'x': 'Int'})
        self.assertEqual(result.smt, '(=> (and (not (= |x| 0)) (<= |x| 4)) (not (= |x| 9)))')

    def test_distinguishes_truncation_floor_and_zero_totalization(self):
        symbols = {'x': 'Int', 'y': 'Int'}
        trunc = parse('x ÷ y', symbols).smt
        floor = parse('x / y', symbols).smt
        self.assertNotEqual(trunc, floor)
        self.assertIn('(xor (< |x| 0) (< |y| 0))', trunc)
        self.assertIn('(ite (= |y| 0) 0', trunc)
        self.assertEqual(parse('Z.quot x y', symbols).smt, trunc)
        self.assertEqual(parse('Z.rem x y', symbols).smt, parse('x % y', symbols).smt)
        self.assertIn('(mod ', parse('x % y', symbols).smt)
        self.assertIn('(ite (= |y| 0) |x|', parse('x % y', symbols).smt)

    def test_exports_typed_conditions_with_source_and_residual_heap(self):
        text = '''(* nested (* ignored *) comment *)
Definition safety := forall (x: Z) (H: x >= 0),
  arbitrary_heap x |-- “ x + 1 > 0 ” && emp.
Definition pure := forall (x: Z) (H: x = 2), x * x = 4.
Definition unsupported := forall (xs: list Z), True.
'''
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            source = root / 'goals.v'
            source.write_text(text)
            report = export_goals(source, root / 'out')
            self.assertEqual(len(report['queries']), 2)
            self.assertFalse(report['program_verified'])
            self.assertEqual(report['goals'][2]['status'], 'unsupported')
            first = report['queries'][0]
            self.assertEqual(first['kind'], 'pure-sufficient-condition')
            self.assertTrue(first['residual_heap'])
            script = (root / 'out' / first['file']).read_text()
            self.assertIn('(declare-const |x| Int)', script)
            self.assertIn('(assert (>= |x| 0))', script)
            self.assertNotIn('arbitrary_heap', script)
            self.assertEqual(json.loads((root / 'out/manifest.json').read_text()), report)

    def test_rejects_unknown_operator_in_any_hypothesis(self):
        with self.assertRaises(Unsupported):
            binders('forall (x: Z) (H: mystery x), x = x')

    def test_rocq_propositions_are_not_bool_values_or_extensional_equalities(self):
        self.assertEqual(parse('b = true', {'b': 'Bool'}).sort, 'Prop')
        self.assertEqual(parse('True <-> 0 = 0', {}).sort, 'Prop')
        for source in ('(0 = 0) = True', 'true /\\ false', 'True = false'):
            with self.subTest(source=source), self.assertRaises(Unsupported):
                parse(source, {})
        with self.assertRaises(Unsupported):
            binders('forall (INT_MAX: Z), INT_MAX = 0')

    def test_source_hash_is_the_original_byte_sequence(self):
        import hashlib
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            source = root / 'windows.v'
            content = b'Definition goal :=\r\nforall (x: Z), x = x.\r\n'
            source.write_bytes(content)
            report = export_goals(source, root / 'out')
            self.assertEqual(report['source_sha256'], hashlib.sha256(content).hexdigest())
            self.assertEqual(len(report['queries']), 1)
            row = report['queries'][0]
            self.assertEqual(row['query_sha256'], hashlib.sha256((root/'out'/row['file']).read_bytes()).hexdigest())


if __name__ == '__main__':
    unittest.main()
