import json
from pathlib import Path
import socket
import sys
import tempfile
import time
import unittest
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration import qcp_native_backend as bridge
from tools.integration.qcp import Unsupported
from tools.integration.qcp_native import formula_query



class NativeBackendTests(unittest.TestCase):
    def test_single_formula_is_not_negated_or_weakened(self):
        script, signature = formula_query('x_7*x_7 < 0 /\\ f(x_7) = 2')
        self.assertIn('(assert (and (< (* |x_7| |x_7|) 0) (= (|f| |x_7|) 2)))', script)
        self.assertEqual(script.count('(assert '), 1)
        self.assertEqual(signature['logic'], 'QF_UFNIA')
        for formula in ('x_0', 'True', 'x_0 / 2 = 0'):
            with self.subTest(formula=formula), self.assertRaises(Unsupported):
                formula_query(formula)

    def test_typed_results_and_smtlib_boundaries_are_checked(self):
        for backend in ('xolver', 'z3'):
            for label in ('sat', 'unsat', 'unknown', 'sat extra'):
                with self.subTest(backend=backend, label=label), tempfile.TemporaryDirectory() as name:
                    session = bridge.BackendSession(backend, Path('/solver'), Path('/guard'))
                    channel = MagicMock(max_bytes=64 * 1024**2)
                    channel.process.pid = 123
                    channel.remaining.return_value = 1
                    channel.diagnostics.return_value = (b'', 0)
                    channel.argv = session.channel.argv
                    session.channel = channel
                    if backend == 'xolver':
                        value = json.dumps(dict(result=label)).encode()
                        response = json.dumps(dict(version=1, results=[dict(
                            id='0', ok=True, payload=list(value), error='')])).encode()
                        channel.read_exact.side_effect = [bridge.HEADER.pack(len(response)), response]
                    else:
                        channel.read_line.side_effect = [(label + '\n').encode(), b'qcp-query-0-done\n']
                    output = Path(name) / 'query'
                    row = bridge.decide('TT', session, output, time.monotonic_ns())
                    self.assertEqual(row['result'], label if label != 'sat extra' else 'error')
                    self.assertFalse(row['program_verified'])
                    self.assertEqual(json.loads((output / 'record.json').read_text()), row)
                    if label == 'sat extra':
                        channel.close.assert_called_once()
                    else:
                        self.assertEqual(row['process_pid'], 123)
                        self.assertEqual(session.ordinal, 1)

    def test_unsupported_and_expired_queries_never_invoke_a_solver(self):
        session = bridge.BackendSession('xolver', Path('/solver'), Path('/guard'))
        with tempfile.TemporaryDirectory() as name, patch.object(session, 'solve') as invoke:
            for index, (formula, started, expected) in enumerate([
                    ('mystery = 1', time.monotonic_ns(), 'unsupported'),
                    ('TT', time.monotonic_ns() - bridge.WALL_NS, 'timeout')]):
                row = bridge.decide(formula, session, Path(name) / str(index), started)
                self.assertEqual(row['result'], expected)
            invoke.assert_not_called()
            self.assertIsNone(session.channel.process)

    def test_both_backends_receive_identical_formulas_and_reusable_process_caps(self):
        rows = []
        with tempfile.TemporaryDirectory() as name:
            for backend in ('xolver', 'z3'):
                session = bridge.BackendSession(backend, Path('/' + backend), Path('/guard'))
                with patch.object(session, 'solve', return_value=dict(result='unsat')) as invoke:
                    row = bridge.decide('x_0 < x_0', session, Path(name) / backend,
                                        time.monotonic_ns())
                    rows.append(row)
                    self.assertEqual(invoke.call_args.args[0],
                                     formula_query('x_0 < x_0')[0])
                self.assertEqual(session.channel.argv[:4],
                                 ('/guard', 'prlimit', '--as=17179869184', '--'))
                self.assertFalse(any(arg.startswith('--cpu') for arg in session.channel.argv))
                if backend == 'z3':
                    self.assertEqual(session.channel.argv[-1], '-in')
        self.assertEqual(rows[0]['query_sha256'], rows[1]['query_sha256'])

    def test_wrong_boundary_and_expired_exchange_close_the_session(self):
        with tempfile.TemporaryDirectory() as name:
            session = bridge.BackendSession('z3', Path('/solver'), Path('/guard'))
            with patch.object(session.channel, 'write'), patch.object(session.channel,
                    'read_line', side_effect=[b'sat\n', b'stale-boundary\n']), \
                    patch.object(session.channel, 'close') as close:
                row = bridge.decide('TT', session, Path(name) / 'boundary', time.monotonic_ns())
                self.assertEqual(row['result'], 'error')
                close.assert_called_once()
            session = bridge.BackendSession('z3', Path('/solver'), Path('/guard'))
            with patch.object(session, 'solve', side_effect=TimeoutError('deadline')), \
                    patch.object(session.channel, 'close') as close:
                row = bridge.decide('TT', session, Path(name) / 'timeout', time.monotonic_ns())
                self.assertEqual(row['result'], 'timeout')
                close.assert_called_once()

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
