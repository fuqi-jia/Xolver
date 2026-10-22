"""Adversarial tests for the evidence harness; no solver needed."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "run_regression", ROOT / "tools/regression/run_regression.py")
harness = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = harness
spec.loader.exec_module(harness)


class RegressionContract(unittest.TestCase):
    def run_fake(self, program, expected="pass"):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            case = root / "input.smt2"
            case.write_text("; (set-info :status unsat)\n(set-info :status sat)\n")
            solver = root / "fake solver"
            solver.write_text("#!/usr/bin/env python3\nimport sys\n" + program + "\n")
            solver.chmod(0o755)
            return harness.run_case(str(case), str(solver), 5, expected)

    def test_opposite_verdict_never_exempted(self):
        for tag in ("pass", "known-fail", "known-unsound"):
            self.assertEqual(self.run_fake("print('unsat')", tag).verdict, "UNSOUND")

    def test_crash_after_correct_token_is_error(self):
        self.assertEqual(self.run_fake("print('sat'); sys.exit(1)", "known-unsound").verdict, "ERROR")

    def test_stderr_is_not_a_verdict(self):
        self.assertEqual(self.run_fake("print('sat'); print('unsat', file=sys.stderr)").verdict, "PASS")
        self.assertEqual(self.run_fake("print('sat', file=sys.stderr)").verdict, "ERROR")

    def test_only_explicit_completeness_gaps_allow_unknown(self):
        self.assertEqual(self.run_fake("print('unknown')").verdict, "UNEXPECTED_FAIL")
        self.assertEqual(self.run_fake("print('unknown')", "known-fail").verdict, "KNOWN_FAIL")

    def test_malformed_result_is_not_accepted(self):
        self.assertEqual(self.run_fake("print('sat garbage')").verdict, "ERROR")

    def test_manifest_sections_do_not_leak(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / harness.MANIFEST_NAME).write_text(
                "## known-fail\n- `a.smt2`\n## resolved\n- `b.smt2`\n")
            self.assertEqual(harness.load_manifest(root), {"a.smt2": "known-fail"})


if __name__ == "__main__":
    unittest.main()
