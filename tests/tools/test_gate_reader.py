import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("gate_reader", ROOT / "tools/remote/check_gate.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class GateReaderTests(unittest.TestCase):
    def test_crashes_and_timeouts_do_not_retract_wrong_answers(self):
        for status in ('error', 'timeout', 'unknown'):
            with self.subTest(status=status):
                self.assertTrue(gate.contradicts({'status': status, 'stdout': 'unsat\n'}, 'sat'))

    def test_later_answer_does_not_erase_an_earlier_contradiction(self):
        self.assertTrue(gate.contradicts({'status': 'sat', 'stdout': 'unsat\nsat\n'}, 'sat'))
        self.assertTrue(gate.contradicts({'status': 'unknown', 'stdout': 'sat\nunknown\n'}, 'unsat'))

    def test_diagnostics_are_not_verdicts(self):
        self.assertFalse(gate.contradicts({'stdout': '(error "unsat")\nsat\n', 'stderr': 'unsat\n'}, 'sat'))
        self.assertFalse(gate.contradicts({'stdout': 'unsat extra\n'}, 'sat'))

    def test_no_verdict_or_no_oracle_is_not_a_wrong_answer(self):
        self.assertFalse(gate.contradicts({'status': 'timeout', 'stdout': ''}, 'sat'))
        self.assertFalse(gate.contradicts({'stdout': 'sat\n'}, None))

    def test_incremental_answers_have_separate_expectations(self):
        self.assertFalse(gate.contradicts({'stdout': 'unsat\nsat\n'}, ['unsat', 'sat']))
        self.assertTrue(gate.contradicts({'stdout': 'sat\nsat\n'}, ['unsat', 'sat']))

    def test_timeout_prefix_is_checked_against_the_corresponding_queries(self):
        self.assertFalse(gate.contradicts({'status': 'timeout', 'stdout': 'unsat\n'}, ['unsat', 'sat']))
        self.assertTrue(gate.contradicts({'status': 'timeout', 'stdout': 'sat\n'}, ['unsat', 'sat']))

    def test_missing_or_extra_answers_are_process_errors(self):
        self.assertEqual(gate.checked_attempt({'status': 'sat', 'stdout': 'sat\n'}, 2)['status'], 'error')
        self.assertEqual(gate.checked_attempt({'status': 'sat', 'stdout': 'sat\nsat\n'}, 1)['status'], 'error')
        self.assertEqual(gate.checked_attempt({'status': 'timeout', 'stdout': 'sat\n'}, 2)['status'], 'timeout')
        self.assertEqual(gate.checked_attempt({'status': 'sat', 'stdout': 'unknown\nsat\n'}, 2)['status'], 'unknown')

    def test_query_count_ignores_comments_strings_and_quoted_symbols(self):
        source = '; (check-sat)\n(set-info :source "(check-sat) ; ""quoted""")\n'
        source += '(declare-const |(check-sat);| Bool)(check-sat)'
        self.assertEqual(gate.query_profile(source)['queries'], 1)

    def test_empty_push_pop_normalized_only_in_oracle_copy(self):
        source = '(set-info :status sat)(push)(check-sat)(pop)(check-sat)'
        profile = gate.query_profile(source)
        self.assertEqual(profile['queries'], 2)
        self.assertEqual(profile['expected'], 'sat')
        self.assertIn('(push 1)', profile['oracle_source'])
        self.assertIn('(pop 1)', profile['oracle_source'])
        self.assertNotIn(':status', profile['oracle_source'])
        self.assertIn('(set-info :status sat)', source)

    def test_deep_terms_do_not_use_python_recursion(self):
        source = '(assert ' + '(not ' * 2000 + 'true' + ')' * 2000 + ')(check-sat)'
        profile = gate.query_profile(source)
        self.assertEqual(profile['queries'], 1)
        self.assertEqual(profile['oracle_source'].count('(not '), 2000)

    def test_paired_timeouts_with_a_wrong_verdict_fail_the_run(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'nia').mkdir()
            (root / 'nia/input.smt2').write_text('(set-info :status sat)\n(assert true)(check-sat)\n')
            solver = root / 'solver'; solver.write_text('fake solver for a mocked process')
            argv = ['check_gate', '--solver', str(solver), '--baseline', str(solver),
                    '--output', str(root / 'out'), '--root', str(root), '--logics', 'nia',
                    '--generated', '0', '--z3', 'unused', '--cvc5', 'unused']
            attempts = [{'status': 'timeout', 'stdout': '', 'stderr': '', 'rc': None},
                        {'status': 'timeout', 'stdout': 'unsat\n', 'stderr': '', 'rc': None}]
            with patch.object(sys, 'argv', argv), patch.object(gate, 'run', side_effect=attempts), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(gate.main(), 1)
            result = json.loads((root / 'out/report.json').read_text())
            self.assertEqual(result['metrics']['wrong_answers'], 1)
            self.assertEqual(result['records'][0]['candidate'][0]['stdout'], 'unsat\n')

    def test_incremental_main_uses_oracle_sequence_and_keeps_failed_attempts(self):
        for wrong_prefix in (False, True):
            with self.subTest(wrong_prefix=wrong_prefix), tempfile.TemporaryDirectory() as directory:
                root = Path(directory); (root / 'nia').mkdir()
                source = '(set-info :status sat)(push)(assert false)(check-sat)(pop)(check-sat)'
                path = root / 'nia/input.smt2'; path.write_text(source)
                solver = root / 'solver'; solver.write_text('fake')
                argv = ['check_gate', '--solver', str(solver), '--baseline', str(solver),
                        '--output', str(root / 'out'), '--root', str(root), '--logics', 'nia',
                        '--generated', '0', '--z3', 'z3', '--cvc5', 'cvc5']
                good = {'status': 'sat', 'stdout': 'unsat\nsat\n', 'stderr': '', 'rc': 0}
                bad = {'status': 'timeout', 'stdout': 'sat\n', 'stderr': '', 'rc': None}
                attempts = [good, good, good, bad if wrong_prefix else good]
                if wrong_prefix:
                    attempts += [good, good]
                with patch.object(sys, 'argv', argv), patch.object(gate, 'run', side_effect=attempts), contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(gate.main(), int(wrong_prefix))
                result = json.loads((root / 'out/report.json').read_text())
                self.assertEqual(result['records'][0]['expected_answers'], ['unsat', 'sat'])
                self.assertEqual(result['metrics']['wrong_answers'], int(wrong_prefix))
                self.assertEqual(result['metrics']['oracle_checked'], 1)
                oracle = Path(result['records'][0]['oracle_input']['path']).read_text()
                self.assertNotIn(':status', oracle)
                self.assertIn('(push 1)', oracle)
                self.assertEqual(path.read_text(), source)


if __name__ == '__main__':
    unittest.main()
