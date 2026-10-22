"""Certificate boundary tests. Kernel acceptance/rejection runs on Panda1."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/proof"))
import pa_trace
from isabelle_pa import Query, bundle


def fixture():
    return {"schema": "xolver-pa-qe-obligations/1", "status": "generated-unchecked",
            "verdict": "sat", "step_count": 1, "closed": [[]], "steps": [
                {"variable": "0", "before": [[{"coefficients": [["0", "-1"]],
                 "constant": "7", "divisor": "0", "negated": False}]], "after": [[]]}]}


class TraceBoundary(unittest.TestCase):
    def test_all_steps_are_proved_and_oracle_dependencies_checked(self):
        trace = fixture()
        theory = Query("(assert true)(check-sat)").theory("sat", certificate=trace)
        self.assertIn('lemma qe_step_0:', theory)
        self.assertIn('lemma result:', theory)
        self.assertIn('@{thms result qe_step_0}', theory)
        self.assertNotIn('sorry', theory)
        # A false step must remain a proof obligation even if result is trivial.
        trace['steps'][0]['after'] = []
        theory = Query("(assert true)(check-sat)").theory("sat", certificate=trace)
        self.assertIn('= False)', theory)
        self.assertIn('@{thms result qe_step_0}', theory)

    def test_malformed_or_incomplete_claims_rejected(self):
        invalid = []
        for key, value in (("status", "kernel-checked"), ("step_count", 0),
                           ("step_count", True), ("closed", []), ("verdict", "unsat")):
            t = fixture(); t[key] = value; invalid.append(t)
        t = fixture(); t['steps'][0]['variable'] = '0)\\<close>'; invalid.append(t)
        t = fixture(); t['steps'][0]['after'] = copy.deepcopy(t['steps'][0]['before']); invalid.append(t)
        t = fixture(); t['steps'][0]['after'] = copy.deepcopy(t['steps'][0]['before'])
        t['steps'][0]['after'][0][0]['coefficients'][0][0] = '1'; invalid.append(t)
        for t in invalid:
            with self.subTest(trace=t), self.assertRaises(pa_trace.InvalidTrace):
                pa_trace.obligations(t, 'sat')
        with self.assertRaises(pa_trace.InvalidTrace):
            pa_trace.load('{"status":1,"status":2}')

    def test_exact_integer_and_literal_validation(self):
        self.assertIn('9' * 5000, pa_trace.integer('9' * 5000))
        for value in (True, 1, 1.5, '01', '-0', '+1', '1/2', '0) ML'):
            with self.subTest(value=value), self.assertRaises(pa_trace.InvalidTrace):
                pa_trace.integer(value)
        for key, value in (("divisor", "-2"), ("negated", 1), ("negated", True),
                           ("coefficients", [["0", "0"]]),
                           ("coefficients", [["0", "1"], ["0", "2"]])):
            t = fixture(); t['steps'][0]['before'][0][0][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(pa_trace.InvalidTrace):
                pa_trace.obligations(t, 'sat')

    def test_bundle_freezes_certificate_with_explicit_trust_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'proof'
            record = bundle('(assert true)(check-sat)', 'sat', output, certificate=fixture())
            self.assertEqual(record['status'], 'generated-unchecked')
            self.assertEqual(record['qe_steps'], 1)
            self.assertIn('not proved', record['certificate_scope'])
            self.assertEqual(json.loads((output / 'certificate.json').read_text()), fixture())


@unittest.skipUnless(os.environ.get('XOLVER_TEST_SOLVER'), 'requires the server solver')
class NativeTraceCLI(unittest.TestCase):
    def invoke(self, directory, source, *options):
        input_path, certificate = Path(directory) / 'input.smt2', Path(directory) / 'certificate.json'
        input_path.write_text(source)
        result = subprocess.run([os.environ['XOLVER_TEST_SOLVER'], 'solve', str(input_path),
                                 '--produce-pa-certificate', str(certificate), *options],
                                capture_output=True, text=True, timeout=30)
        return result, certificate

    def test_sat_unsat_and_interactive_query(self):
        for source, verdict in (
            ('(assert (forall ((x Int)) (exists ((y Int)) (> y x))))(check-sat)', 'sat'),
            ('(assert (exists ((x Int)) (forall ((y Int)) (> x y))))(check-sat)', 'unsat'),
            ('(declare-const x Int)(assert (= x 9))(check-sat)(get-value (x))', 'sat'),
            ('(check-sat)', 'sat')):
            with self.subTest(source=source), tempfile.TemporaryDirectory() as directory:
                result, path = self.invoke(directory, '(set-logic LIA)' + source)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                trace = pa_trace.load(path.read_text())
                pa_trace.obligations(trace, verdict)
                self.assertIn('generated-unchecked', result.stderr)

    def test_no_stale_file_overwrite_or_unknown_certificate(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'certificate.json'; path.write_text('prior evidence')
            result, _ = self.invoke(directory, '(set-logic LIA)(assert true)(check-sat)')
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(path.read_text(), 'prior evidence')
        with tempfile.TemporaryDirectory() as directory:
            result, path = self.invoke(directory,
                '(set-logic ALL)(declare-const x Int)(assert (= (* x x) 2))(check-sat)')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('unknown', result.stdout.splitlines())
            self.assertFalse(path.exists())

    def test_multiple_queries_cannot_share_a_certificate(self):
        with tempfile.TemporaryDirectory() as directory:
            result, path = self.invoke(directory, '(set-logic LIA)(check-sat)(check-sat)')
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(path.exists())


if __name__ == '__main__':
    unittest.main()
