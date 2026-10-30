import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import Unsupported
from tools.integration.qcp_native import NativeCheck, NativeParser, export_trace, extract_checks, query


def trace(source, target, flag=0):
    return ('[QCP_DEBUG_SMT] Source SMT:\n' + source + '\n'
            '[QCP_DEBUG_SMT] Target SMT:\n' + target + '\n'
            '[QCP_DEBUG_SMT] SingleSmtPropCheck flag=' + str(flag) +
            ' (-1 false, 0 proved, 1 unknown)\n')


def parse(source):
    return NativeParser(source, {}, {}).parse()


class NativeQcpTests(unittest.TestCase):
    def test_negation_scope_and_integer_bounds(self):
        result = parse('NOT x_0 = 0 /\\ x_0 <= SMT_INT32_MAX -> x_0 <> 1')
        self.assertEqual(result.smt, '(=> (and (not (= |x_0| 0)) (<= |x_0| 2147483647)) (not (= |x_0| 1)))')
        for bits in [8, 16, 32, 64]:
            self.assertEqual(parse('(-(SMT_INT%d_MAX + 1))' % bits).smt,
                             '(- (+ %d 1))' % ((1 << (bits - 1)) - 1))

    def test_native_functions_remain_uninterpreted(self):
        check = NativeCheck('TT', 'Zgcd(x_0, x_1) = Omod(x_0, x_1)', 1, (0, 0), (0, 0))
        script, metadata = query(check)
        self.assertIn('(declare-fun |Zgcd| (Int Int) Int)', script)
        self.assertIn('(declare-fun |Omod| (Int Int) Int)', script)
        self.assertIn('(|Zgcd| |x_0| |x_1|)', script)
        self.assertNotIn('(mod ', script)
        self.assertNotIn('qcp.gcd', script)
        self.assertEqual(metadata['logic'], 'QF_UFLIA')
        # Symmetry is not a property of an arbitrary native function name.
        self.assertNotEqual(parse('Zgcd(x_0, x_1)'), parse('Zgcd(x_1, x_0)'))

    def test_arity_and_type_conflicts_reject_the_entire_check(self):
        for target in ['f(x_0, x_1) = 0', 'x_0(TT) = 0', 'f(TT) = 0']:
            with self.subTest(target=target), self.assertRaises(Unsupported):
                query(NativeCheck('f(x_0) = 0', target, 0, (0, 0), (0, 0)))

    def test_unknown_symbols_and_dialect_operations_are_not_guessed(self):
        for text in ['unknown = 0', 'p_1 /\\ TT', 'True', 'Z.quot x_0 x_1',
                     'x_0 % x_1 = 0', 'x_0 / x_1 = 0', 'x_0 ^ 2 = 0', 'TT + 1 = 0',
                     'x_0 < x_1 < x_2', 'TT(TT)']:
            with self.subTest(text=text), self.assertRaises(Unsupported):
                parse(text)

    def test_logic_follows_terms_not_program_name(self):
        for target, logic in [('x_0 + 2*x_1 > 0', 'QF_LIA'),
                              ('x_0*x_1 > 0', 'QF_NIA'),
                              ('f(x_0*x_1) > 0', 'QF_UFNIA')]:
            _, details = query(NativeCheck('TT', target, 0, (0, 0), (0, 0)))
            self.assertEqual(details['logic'], logic)

    def test_duplicate_calls_and_all_native_flags_are_retained(self):
        text = 'unrelated diagnostics\n' + trace('TT', 'x_0 = x_0', -1) * 2 + trace('TT', 'FF', 1)
        checks = extract_checks(text)
        self.assertEqual(len(checks), 3)
        self.assertEqual([c.native_flag for c in checks], [-1, -1, 1])
        for check in checks:
            self.assertEqual(text[slice(*check.source_span)].strip(), check.source)
            self.assertEqual(text[slice(*check.target_span)].strip(), check.target)

    def test_incomplete_or_unpaired_trace_is_rejected(self):
        good = trace('TT', 'TT')
        for text in ['', good[:good.index('[QCP_DEBUG_SMT] SingleSmt')],
                     '[QCP_DEBUG_SMT] Target SMT:\nTT\n',
                     good[good.index('[QCP_DEBUG_SMT] SingleSmt'):],
                     trace('TT', 'TT', 2), good + '[QCP_DEBUG_SMT] Source SMT:\nTT\n']:
            with self.subTest(text=text), self.assertRaises(Unsupported):
                extract_checks(text)

    def test_export_keeps_unsupported_conditions_and_does_not_verify_a_program(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name);source = root/'trace.txt'
            source.write_text(trace('TT', 'x_0 = x_0') * 2 + trace('TT', 'mystery = 0', 1))
            result = export_trace(source, root/'queries')
            self.assertEqual(result['captured_checks'], 3)
            self.assertEqual(len(result['queries']), 2)
            self.assertEqual(result['unique_queries'], 1)
            self.assertEqual(len(result['unsupported']), 1)
            self.assertFalse(result['program_verified'])
            self.assertIsNone(result['internal_qcp_queries_total'])
            self.assertFalse(result['generation_completion_marker'])
            self.assertEqual(json.loads((root/'queries/manifest.json').read_text()), result)

    def test_resource_guards_precede_python_recursion_overflow(self):
        with self.assertRaises(Unsupported):
            parse('(' * 170 + 'TT' + ')' * 170)

    def test_ground_arithmetic_matches_an_independent_smt_evaluator(self):
        # Parse only the exported SMT syntax here, independently of the native
        # Pratt parser. The arbitrary Zgcd interpretation must stay arbitrary.
        def tree(tokens):
            token = next(tokens)
            if token != '(':
                return token
            result = []
            while tokens.peek != ')':
                result.append(tree(tokens))
            next(tokens)
            return result
        class Tokens:
            def __init__(self, text):
                self.items = iter(re.findall(r'\(|\)|[^\s()]+', text));self.peek = next(self.items, None)
            def __iter__(self):return self
            def __next__(self):
                previous = self.peek;self.peek = next(self.items, None)
                if previous is None:raise StopIteration
                return previous
        def evaluate(value):
            if isinstance(value, str):
                if value in ('true', 'false'):return value == 'true'
                return int(value)
            op, *children = value;args = [evaluate(c) for c in children]
            return {'+': lambda: args[0] + args[1], '*': lambda: args[0] * args[1],
                    '-': lambda: -args[0] if len(args)==1 else args[0]-args[1],
                    '=': lambda: args[0]==args[1], '<': lambda: args[0]<args[1],
                    '<=': lambda: args[0]<=args[1], '>': lambda: args[0]>args[1],
                    '>=': lambda: args[0]>=args[1], 'not': lambda: not args[0],
                    'and': lambda: all(args), 'or': lambda: any(args),
                    '=>': lambda: not args[0] or args[1],
                    '|Zgcd|': lambda: 2*args[0]-args[1]}[op]()
        for x in range(-4, 5):
            for y in range(-4, 5):
                a,b='(%d)'%x,'(%d)'%y
                samples=[(f'NOT {a} = {b} /\\ {a}+{b} <= 3', x!=y and x+y<=3),
                         (f'{a}*{b}-{a} >= {b} -> {a} < 4 \\/ FF', not(x*y-x>=y) or x<4),
                         (f'Zgcd({a},{b}) = 2*{a}-{b}', True)]
                for text, expected in samples:
                    with self.subTest(text=text):
                        self.assertEqual(evaluate(tree(Tokens(parse(text).smt))), expected)


if __name__ == '__main__':
    unittest.main()
