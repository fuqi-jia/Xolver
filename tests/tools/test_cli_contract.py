import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SOLVER = os.environ.get('XOLVER_TEST_SOLVER')


@unittest.skipUnless(SOLVER, 'XOLVER_TEST_SOLVER must name the server binary')
class CliEvidenceContract(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def solve(self, source):
        path = self.root / 'input.smt2'
        path.write_text(source)
        cert = self.root / 'certificate.smt2'
        result = subprocess.run([SOLVER, 'solve', str(path), '--certify', str(cert)],
                                capture_output=True, text=True, timeout=15)
        return result, cert

    def test_positive_numeric_certificate(self):
        result, cert = self.solve('(set-logic QF_LIA)(declare-const x Int)'
                                  '(assert (= x 42))(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(cert.is_file())

    def test_unsupported_model_evaluation_cannot_certify(self):
        result, cert = self.solve('(set-logic QF_DT)(declare-datatype Color ((red) (blue)))'
                                  '(declare-const c Color)(assert ((_ is red) c))(check-sat)')
        self.assertIn('sat', result.stdout.splitlines())
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(cert.exists())

    def proof_check(self, assumed, base_name='proof'):
        base = self.root / base_name
        Path(str(base) + '.cnf').write_text(
            'c xolver-proof: 1 original clauses, %d theory lemmas assumed as axioms\np cnf 0 1\n0\n' % assumed)
        Path(str(base) + '.drat').write_text('0\n')
        checker = self.root / 'checker with spaces'
        checker.write_text("#!/bin/sh\nprintf 's VERIFIED\\n'\n")
        checker.chmod(0o755)
        return subprocess.run([SOLVER, 'proof-check', str(base), '--drat-trim', str(checker)],
                              cwd=self.root, capture_output=True, text=True, timeout=15)

    def test_skeleton_is_not_a_complete_proof(self):
        result = self.proof_check(1)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('skeleton', result.stderr)

    def test_checker_arguments_are_literal(self):
        result = self.proof_check(0, "p'$(touch injected)")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse((self.root / 'injected').exists())

    def test_batch_assumptions_are_not_discarded(self):
        path = self.root / 'assuming.smt2'
        path.write_text('(set-logic QF_UF)(declare-const p Bool)'
                        '(assert p)(check-sat-assuming ((not p)))')
        result = subprocess.run([SOLVER, 'solve', str(path)], capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.strip(), 'unsat')

    def test_multiquery_scripts_do_not_solve_the_wrong_context(self):
        path = self.root / 'sequential.smt2'
        path.write_text('(set-logic QF_UF)(check-sat)(assert false)(check-sat)')
        result = subprocess.run([SOLVER, 'solve', str(path)], capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['sat', 'unsat'])

    def test_assumptions_do_not_leak_to_later_queries(self):
        path = self.root / 'assumption-scopes.smt2'
        path.write_text('(set-logic QF_UF)(declare-const p Bool)(assert p)'
                        '(check-sat-assuming ((not p)))'
                        '(check-sat)(check-sat-assuming ())')
        result = subprocess.run([SOLVER, 'solve', str(path)], capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['unsat', 'sat', 'sat'])

    def test_get_value_tracks_each_query_model(self):
        path = self.root / 'values.smt2'
        path.write_text('(set-logic QF_LIA)(declare-const x Int)(push 1)'
                        '(assert (= x 1))(check-sat)(get-value (x))(pop 1)'
                        '(assert (= x 2))(check-sat)(get-value (x))')
        result = subprocess.run([SOLVER, 'solve', str(path)], capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines(), ['sat', '((x 1))', 'sat', '((x 2))'])

    def test_bitvector_models_and_values_preserve_width_and_query_scope(self):
        path = self.root / 'bitvector-values.smt2'
        path.write_text('(set-logic BV)(set-option :produce-models true)'
                        '(declare-const x (_ BitVec 4))(declare-const unused (_ BitVec 4))'
                        '(push 1)(assert (= (bvadd x #x1) #x0))(check-sat)'
                        '(get-value (x (bvadd x #x1)))(get-model)(pop 1)'
                        '(assert (= x #x2))(check-sat)(get-value (x))')
        result = subprocess.run([SOLVER, 'solve', str(path)], capture_output=True,
                                text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r'\(\(x \(_ bv15 4\)\)\(\(bvadd x (?:#x1|#b0001)\) \(_ bv0 4\)\)\)')
        self.assertIn('(define-fun x () (_ BitVec 4) (_ bv15 4))', result.stdout)
        self.assertIn('(define-fun unused () (_ BitVec 4) (_ bv0 4))', result.stdout)
        self.assertTrue(result.stdout.rstrip().endswith('((x (_ bv2 4)))'), result.stdout)

    def test_proof_export_with_synthesized_theory_atoms(self):
        regression = Path(__file__).resolve().parents[1] / 'regression'
        for case in [
            'alia/alia_010_unsat_const_fallthrough.smt2',
            'auflia/auflia_002_unsat_row2_arith_index.smt2',
            'aufnia/aufnia_002_unsat_uf_congruence.smt2',
            'aufnia/aufnia_003_unsat_uf_array_congruence.smt2',
        ]:
            with self.subTest(case=case):
                result = subprocess.run(
                    [SOLVER, 'solve', str(regression / case), '--produce-proof',
                     str(self.root / Path(case).stem)],
                    capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout.strip(), 'unsat')


if __name__ == '__main__':
    unittest.main()
