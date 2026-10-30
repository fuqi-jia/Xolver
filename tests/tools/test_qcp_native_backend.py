import json
from pathlib import Path
import socket
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration import qcp_native_backend as bridge
from tools.integration.qcp import Unsupported
from tools.integration.qcp_native import formula_query


def timing(returncode=0, timed_out=False):
    return dict(returncode=returncode, timed_out=timed_out, budget_overrun=False, seconds=0.001)


class NativeBackendTests(unittest.TestCase):
    def test_single_formula_is_not_negated_or_weakened(self):
        script, signature = formula_query('x_7*x_7 < 0 /\\ f(x_7) = 2')
        self.assertIn('(assert (and (< (* |x_7| |x_7|) 0) (= (|f| |x_7|) 2)))', script)
        self.assertEqual(script.count('(assert '), 1)
        self.assertEqual(signature['logic'], 'QF_UFNIA')
        for formula in ('x_0', 'True', 'x_0 / 2 = 0'):
            with self.subTest(formula=formula), self.assertRaises(Unsupported):
                formula_query(formula)

    def test_only_a_strict_definite_label_can_be_returned_to_the_host(self):
        samples = [(b'sat\n', 0, False, 'sat'), (b'unsat\n', 0, False, 'unsat'),
                   (b'unknown\n', 0, False, 'unknown'), (b'sat\nextra', 0, False, 'error'),
                   (b'unsat\n', 1, False, 'error'), (b'unsat\n', 0, True, 'timeout')]
        with tempfile.TemporaryDirectory() as name:
            for number, (stdout, code, expired, expected) in enumerate(samples):
                output = Path(name) / str(number)
                with self.subTest(expected=expected), patch.object(bridge, 'run_with_budget',
                        return_value=(stdout, b'', timing(code, expired))) as invoke:
                    row = bridge.decide('TT', 'xolver', Path('/solver'), Path('/guard'),
                                        output, time.monotonic_ns())
                    self.assertEqual(row['result'], expected)
                    self.assertEqual(invoke.call_count, 1)
                    self.assertFalse(row['program_verified'])
                    self.assertEqual(json.loads((output / 'record.json').read_text()), row)

    def test_unsupported_and_expired_queries_never_invoke_a_solver(self):
        with tempfile.TemporaryDirectory() as name, patch.object(bridge, 'run_with_budget') as invoke:
            for index, (formula, started, expected) in enumerate([
                    ('mystery = 1', time.monotonic_ns(), 'unsupported'),
                    ('TT', time.monotonic_ns() - bridge.WALL_NS, 'timeout')]):
                row = bridge.decide(formula, 'xolver', Path('/solver'), Path('/guard'),
                                    Path(name) / str(index), started)
                self.assertEqual(row['result'], expected)
            invoke.assert_not_called()

    def test_both_selected_backends_receive_the_same_formula_and_caps(self):
        with tempfile.TemporaryDirectory() as name, patch.object(bridge, 'run_with_budget',
                return_value=(b'unsat\n', b'', timing())) as invoke:
            rows = [bridge.decide('x_0 < x_0', backend, Path('/' + backend), Path('/guard'),
                                  Path(name) / backend, time.monotonic_ns())
                    for backend in ('xolver', 'z3')]
            self.assertEqual(rows[0]['query_sha256'], rows[1]['query_sha256'])
            for call in invoke.call_args_list:
                command, budget, environment = call.args
                self.assertEqual(command[:4], ['/guard', 'prlimit', '--as=17179869184', '--cpu=62:63'])
                self.assertGreater(budget, 0)
                self.assertLessEqual(budget, 60)
                self.assertNotIn('LD_PRELOAD', environment)
                self.assertFalse(any(k.startswith('XOLVER_QCP_') for k in environment))
            self.assertIn('solve', invoke.call_args_list[0].args[0])
            self.assertIn('-T:60', invoke.call_args_list[1].args[0])

    def test_socket_frames_cannot_turn_truncation_into_an_empty_formula(self):
        left, right = socket.socketpair()
        with left, right:
            right.sendall(b'abc')
            right.shutdown(socket.SHUT_WR)
            with self.assertRaisesRegex(ValueError, 'truncated'):
                bridge.receive(left, 5)
        left, right = socket.socketpair()
        with left, right:
            right.shutdown(socket.SHUT_WR)
            self.assertEqual(bridge.receive(left, bridge.FRAME.size, allow_eof=True), b'')

    def test_solver_controls_and_preload_do_not_leak_into_selected_backends(self):
        with patch.dict(bridge.os.environ, {'LD_PRELOAD': 'injected.so',
                        'XOLVER_QCP_BACKEND': 'xolver', 'EOS_CPU_IDS': '7'}):
            environment = bridge.solver_environment()
            self.assertNotIn('LD_PRELOAD', environment)
            self.assertNotIn('XOLVER_QCP_BACKEND', environment)
            self.assertEqual(environment['EOS_CPU_IDS'], '7')


if __name__ == '__main__':
    unittest.main()
