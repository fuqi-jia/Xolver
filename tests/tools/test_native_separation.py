import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SOLVER = os.environ.get("XOLVER_TEST_SOLVER")
HEADER = "(set-logic ALL)(declare-heap (Int Int))"


@unittest.skipUnless(SOLVER, "requires the server solver")
class NativeSeparation(unittest.TestCase):
    def run_source(self, source, *options):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.smt2"
            path.write_text(source)
            result = subprocess.run([SOLVER, "solve", str(path), *options],
                                    capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def test_heap_snapshot_and_reset(self):
        result = self.run_source(
            HEADER + "(assert sep.emp)(check-sat)(get-model)"
            "(push 1)(assert (not sep.emp))(check-sat)"
            "(pop 1)(check-sat)(get-model)"
            "(reset-assertions)(assert (pto 1 2))(check-sat)(get-model)"
            "(reset)(set-logic QF_LIA)(assert false)(check-sat)")
        verdicts = [line for line in result.stdout.splitlines()
                    if line in ("sat", "unsat", "unknown")]
        self.assertEqual(verdicts, ["sat", "unsat", "sat", "sat", "unsat"])
        self.assertEqual(result.stdout.count("(heap"), 3)
        self.assertIn("(pto 1 2)", result.stdout)

    def test_model_and_spatial_get_value(self):
        result = self.run_source(
            HEADER + "(declare-const |address x| Int)(declare-const y Int)"
            "(assert (= (as sep.nil Int) 17))(assert (= |address x| 0))"
            "(assert (= y (- 123456789012345678901234567890)))"
            "(assert (pto |address x| y))(check-sat)(get-model)"
            "(get-value (|address x| y (as sep.nil Int) sep.emp (pto |address x| y)))",
            "--check-model")
        self.assertNotIn("MODEL_MISMATCH", result.stderr)
        self.assertIn("(define-fun |address x| () Int 0)", result.stdout)
        self.assertIn("(pto 0 (- 123456789012345678901234567890))", result.stdout)
        self.assertIn("((as sep.nil Int) 17)", result.stdout)
        self.assertIn("(sep.emp false)", result.stdout)
        self.assertIn("((pto |address x| y) true)", result.stdout)

    def test_assumptions_do_not_escape_query(self):
        result = self.run_source(
            HEADER + "(declare-const p Bool)(assert (= p sep.emp))"
            "(assert sep.emp)(check-sat-assuming ((not p)))"
            "(check-sat)(get-model)")
        self.assertEqual([line for line in result.stdout.splitlines()
                          if line in ("sat", "unsat", "unknown")], ["unsat", "sat"])

    def test_empty_query_still_has_a_heap_interpretation(self):
        result = self.run_source(HEADER + "(check-sat)(get-model)")
        self.assertIn("(heap", result.stdout)
        self.assertIn("sep.emp", result.stdout)

    def test_reset_redeclaration_and_global_declarations(self):
        result = self.run_source(
            HEADER + "(declare-const x Int)(assert (= x 4))(push 1)"
            "(assert sep.emp)(check-sat)(reset-assertions)"
            "(declare-const x Bool)(assert x)(check-sat)"
            "(reset)(set-logic ALL)(set-option :global-declarations true)"
            "(declare-heap (Int Int))(push 1)(declare-const x Int)(pop 1)"
            "(reset-assertions)(assert (pto x 2))(check-sat)(get-model)")
        self.assertEqual([line for line in result.stdout.splitlines()
                          if line in ("sat", "unsat", "unknown")], ["sat", "sat", "sat"])
        self.assertIn("(heap", result.stdout)

    def test_unsupported_formula_is_not_propositional_sat(self):
        result = self.run_source(
            HEADER + "(declare-const x Int)(assert (pto (* x x) 2))(check-sat)",
            "--verbose")
        self.assertIn("unknown", result.stdout.splitlines())
        self.assertIn("nonlinear", result.stderr)

    def test_arithmetic_models_values_and_incremental_queries(self):
        result = self.run_source(
            HEADER + "(declare-const x Int)(declare-const y Int)"
            "(assert (= (as sep.nil Int) 17))(assert (= x (- 5)))"
            "(assert (= y (mod x (- 2))))(assert (pto (+ x 1) y))"
            "(check-sat)(get-model)(get-value ((div x (- 2)) (pto (+ x 1) y) (> x 0)))"
            "(push 1)(assert (> x 0))(check-sat)(pop 1)(check-sat)",
            "--check-model")
        self.assertEqual([line for line in result.stdout.splitlines()
                          if line in ("sat", "unsat", "unknown")], ["sat", "unsat", "sat"])
        self.assertIn("(pto (- 4) 1)", result.stdout)
        self.assertIn("((div x (- 2)) 3)", result.stdout)
        self.assertRegex(result.stdout, r"\(\(pto \(\+ (?:x 1|1 x)\) y\) true\)")
        self.assertIn("((> x 0) false)", result.stdout)
        self.assertNotIn("MODEL_MISMATCH", result.stderr)


if __name__ == "__main__":
    unittest.main()
