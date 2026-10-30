import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/remote'))
import compare_arithmetic_case as comparison


class ArithmeticComparisonCapture(unittest.TestCase):
    def run_comparison(self, *, invalid_model=False, missing_model=False, validate=True):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'original.smt2'
            source.write_text('(set-logic QF_LRA)\n(declare-const x Real)\n'
                              '(assert (= x 1))\n(check-sat)\n')
            original = source.read_bytes()
            manifest = root / 'manifest.json'
            manifest.write_text(json.dumps(dict(cases=[dict(path=str(source),
                sha256=hashlib.sha256(original).hexdigest(), expected='sat',
                logic='QF_LRA', member='original.smt2')])))
            binaries = {name: root / name for name in ('baseline', 'candidate', 'z3', 'cvc5')}
            for name, binary in binaries.items():
                binary.write_text(name)
            argv = ['compare', '--manifest', str(manifest), '--output', str(root / 'results'),
                    '--index', '0']
            if validate:
                argv.append('--validate-models')
            for name, binary in binaries.items():
                argv += ['--' + name, str(binary)]
            initial = []
            replays = []

            def invoke(command, timeout, environment):
                self.assertEqual(timeout, 60)
                self.assertIn('--as=17179869184', command)
                arguments = command[command.index('--') + 1:]
                query = next(Path(arg) for arg in arguments if arg.endswith('.smt2'))
                timing = dict(returncode=0, seconds=0.1, timed_out=False, budget_overrun=False)
                if query == source:
                    self.assertEqual(query.read_bytes(), original)
                    name = Path(arguments[0]).name
                    self.assertNotIn(name, initial, 'a timed SAT must not be searched again for its model')
                    initial.append(name)
                    flag = '-model' if name == 'z3' else '--produce-models'
                    if not validate:
                        self.assertNotIn(flag, arguments)
                        return b'sat\n', b'', timing
                    self.assertIn(flag, arguments)
                    if missing_model and name == 'candidate':
                        return b'sat\n', b'', timing
                    value = '(- 1)' if invalid_model and name == 'candidate' else '1'
                    return ('sat\n(model (define-fun x () Real ' + value + '))\n').encode(), b'', timing
                self.assertTrue(query.name.endswith('-replay.smt2'), arguments)
                self.assertIn('(assert (= x 1))', query.read_text())
                self.assertIn('(define-fun x', query.read_text())
                replays.append(query.name)
                result = 'unsat' if invalid_model and query.name == 'candidate-replay.smt2' else 'sat'
                return (result + '\n').encode(), b'', timing

            with patch.object(sys, 'argv', argv), \
                    patch.dict(os.environ, {'EOS_CPU_IDS': '7', 'EOS_METRICS_FILE': str(root / 'metrics.json')}), \
                    patch.object(comparison.os, 'sched_getaffinity', return_value={7}), \
                    patch.object(comparison.os, 'sched_setaffinity'), \
                    patch.object(comparison, 'run_with_budget', side_effect=invoke):
                status = comparison.main()
            report = json.loads((root / 'results/case-000/report.json').read_text())
            metrics = json.loads((root / 'metrics.json').read_text())
            self.assertCountEqual(initial, ['baseline', 'candidate', 'z3'])
            return status, report, metrics, replays

    def test_each_solver_exports_and_checks_the_actual_timed_model(self):
        status, report, metrics, replays = self.run_comparison()
        self.assertEqual(status, 0)
        self.assertEqual(metrics['errors'], 0)
        self.assertEqual(report['model_capture'], 'initial-solve')
        self.assertEqual(len(replays), 3)
        for observation in report['observations'].values():
            self.assertTrue(observation['verified'])
            self.assertNotIn('model', observation)

    def test_an_invalid_initial_model_fails_despite_agreeing_sat_verdicts(self):
        status, report, metrics, _ = self.run_comparison(invalid_model=True)
        self.assertEqual(status, 1)
        self.assertEqual(metrics['errors'], 1)
        self.assertFalse(report['wrong_verdict'])
        candidate = report['observations']['candidate']
        self.assertFalse(candidate['verified'])
        self.assertEqual(candidate['replay']['result'], 'unsat')

    def test_a_missing_model_stays_explicit_without_repeating_the_search(self):
        status, report, _, replays = self.run_comparison(missing_model=True)
        self.assertEqual(status, 0)
        self.assertEqual(len(replays), 2)
        candidate = report['observations']['candidate']
        self.assertFalse(candidate['verified'])
        self.assertTrue(candidate.get('model_error'))

    def test_decision_only_mode_keeps_its_existing_output_contract(self):
        status, report, _, replays = self.run_comparison(validate=False)
        self.assertEqual(status, 0)
        self.assertIsNone(report['model_capture'])
        self.assertEqual(replays, [])


if __name__ == '__main__':
    unittest.main()
