import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import (Unsupported, binders, export_goals,
    integer_function_facts, owned_int_ranges, parse, sufficient_leaves)


class QcpAdapterTests(unittest.TestCase):
    def test_signed_gcd_uses_shared_ground_instances_without_answer_unrolling(self):
        symbols = {'a': 'Int', 'b': 'Int'}
        self.assertEqual(parse('Zgcd a b', symbols), parse('Z.gcd b a', symbols))
        term = parse('Zgcd b (a % b) = Zgcd a b', symbols)
        declarations, facts = integer_function_facts([term])
        self.assertEqual(declarations, ['(declare-fun |qcp.gcd| (Int Int) Int)'])
        euclid = [f for f in facts if f['lemma'] == 'Z.gcd_rem + Z.gcd_comm']
        self.assertEqual(len(euclid), 1)
        self.assertIn('(=> (not (= |b| 0))', euclid[0]['assertion'])
        self.assertTrue(any(f['lemma'] == 'Z.gcd_0_r' for f in facts))
        self.assertNotIn('forall', '\n'.join(f['assertion'] for f in facts))
        self.assertEqual(integer_function_facts([parse('a % b = 0', symbols)]), ([], []))
        for source in ['forall (Zgcd: Z), Zgcd = 0', 'forall (Zabs: Z), Zabs = 0']:
            with self.subTest(source=source), self.assertRaises(Unsupported):
                binders(source)

    def test_gcd_ground_facts_hold_for_signed_and_zero_inputs_independently(self):
        import math
        import re
        _, facts = integer_function_facts([parse('Zgcd b (a % b) = Zgcd a b',
                                                   {'a': 'Int', 'b': 'Int'})])
        def expression(tokens):
            token = next(tokens)
            if token != '(':
                return token
            result = []
            while True:
                token = next(tokens)
                if token == ')':
                    return result
                # Push one token back without sharing the source parser.
                import itertools
                child = expression(itertools.chain([token], tokens))
                result.append(child)
        trees = [expression(iter(re.findall(r'\(|\)|[^\s()]+', f['assertion']))) for f in facts]
        def evaluate(tree, values):
            if isinstance(tree, str):
                return values[tree] if tree in values else int(tree)
            op, *children = tree
            args = [evaluate(c, values) for c in children]
            return {'|qcp.gcd|': lambda: math.gcd(*args),
                    '=>': lambda: not args[0] or args[1], 'not': lambda: not args[0],
                    '=': lambda: args[0] == args[1], '>=': lambda: args[0] >= args[1],
                    '<': lambda: args[0] < args[1], '-': lambda: -args[0],
                    'ite': lambda: args[1] if args[0] else args[2],
                    # SMT-LIB integer mod is Euclidean for either divisor sign.
                    'mod': lambda: args[0] % abs(args[1]) if args[1] else 0}[op]()
        for a in range(-12, 13):
            for b in range(-12, 13):
                for fact, tree in zip(facts, trees):
                    with self.subTest(a=a, b=b, lemma=fact['lemma']):
                        self.assertTrue(evaluate(tree, {'|a|': a, '|b|': b}))

    def test_composed_vcs_expand_sufficient_children_without_assuming_parents(self):
        definitions = {'a': 'forall (x: Z), x = x',
                       'b': 'forall (y: Z), y = 0',
                       'c': 'forall (z: Z), z = 1'}
        leaves = sufficient_leaves('a /\\ b \\/ c', definitions)
        self.assertEqual([l['body'] for l in leaves], [definitions['a'], definitions['b']])
        self.assertEqual(leaves[0]['proof_path'][0], dict(direction='left'))
        self.assertEqual(sufficient_leaves('a -> b \\/ c', definitions)[0]['body'], definitions['b'])
        for source in ['missing', 'a /\\ missing', '(a', 'a)']:
            with self.subTest(source=source), self.assertRaises(Unsupported):
                sufficient_leaves(source, definitions)
        with self.assertRaises(Unsupported):
            sufficient_leaves('a', {'a': 'b', 'b': 'a'})

    def test_gcd_parent_and_split_conditions_export_with_independent_query_evidence(self):
        text = '''Definition step := forall (a: Z) (b: Z) (r: Z)
  (H: b <> 0) (Hr: r = Zgcd b (a % b)), r = Zgcd a b.
Definition base := forall (a: Z) (r: Z) (H: r = Zabs a), r = Zgcd a 0.
Definition parent := step \\/ base.
Definition combined := step /\\ base.
Definition implication := base -> step.
'''
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            source = root / 'goals.v'; source.write_text(text)
            report = export_goals(source, root / 'out')
            self.assertEqual([g['status'] for g in report['goals']], ['exported'] * 5)
            self.assertEqual(len(report['queries']), 6)
            parent = next(q for q in report['queries'] if q['name'] == 'parent')
            self.assertEqual(parent['proof_path'], [dict(direction='left'), dict(unfold='step')])
            self.assertTrue(parent['integer_function_facts'])
            script = (root / 'out' / parent['file']).read_text()
            self.assertNotIn('(assert |step|)', script)
            self.assertIn('(declare-fun |qcp.gcd| (Int Int) Int)', script)
            self.assertFalse(report['program_verified'])

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

    def test_owned_cell_ranges_require_complete_positive_assertion_grammar(self):
        cell = '((&("x")) # Int |-> x)'
        symbols = {'x': 'Int', 'y': 'Int', 'p': 'Int'}
        facts = owned_int_ranges(f'({cell} ** ((p # Int |-> (y + 1)) && emp))', symbols)
        self.assertEqual(len(facts), 2)
        self.assertEqual(facts[0]['upper'], '(<= |x| 2147483647)')
        self.assertEqual(facts[1]['lower'], '(<= (- 2147483648) (+ |y| 1))')
        # No partial extraction, even when a supported cell is another conjunct.
        unsafe = [f'{cell} || emp', f'~ {cell}', f'{cell} -* emp',
                  f'EX x, {cell}', f'foo {cell}', f'{cell} ** arbitrary_heap',
                  f'({cell} || emp) ** {cell}', f'~ {cell} && {cell}',
                  f'if True then {cell} else emp && {cell}',
                  'p # UInt |-> x', 'p # Int |-> mystery', 'p # Int |-> true',
                  'p # Int |-> (x = y)', 'p # Int |-> x trailing']
        for assertion in unsafe:
            with self.subTest(assertion=assertion):
                self.assertEqual(owned_int_ranges(assertion, symbols), [])

    def test_typed_cells_strengthen_only_the_antecedent_and_record_derivation(self):
        text = '''Definition owned := forall (x: Z) (y: Z),
  (( &("left") ) # Int |-> x) ** (( &("right") ) # Int |-> y)
  |-- “ x <= INT_MAX ” && “ y >= INT_MIN ” && emp.
Definition unowned := forall (x: Z), emp |-- “ x <= INT_MAX ”.
Definition negative := forall (x: Z),
  ((( &("left") ) # Int |-> x) || emp) |-- “ x <= INT_MAX ”.
'''
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            source = root / 'goals.v'
            source.write_text(text)
            report = export_goals(source, root / 'out')
            facts = report['goals'][0]['derived_assumptions']
            self.assertEqual([f['value'] for f in facts], ['x', 'y'])
            self.assertTrue(all(f['lemma'] == 'store_int_range' for f in facts))
            script = (root / 'out/owned-0.smt2').read_text()
            self.assertIn('(assert (<= |x| 2147483647))', script)
            self.assertIn('(assert (<= (- 2147483648) |y|))', script)
            for name in ('unowned', 'negative'):
                other = (root / 'out' / (name + '-0.smt2')).read_text()
                self.assertNotIn('(assert (<= |x| 2147483647))', other)
            self.assertFalse(report['program_verified'])


if __name__ == '__main__':
    unittest.main()
