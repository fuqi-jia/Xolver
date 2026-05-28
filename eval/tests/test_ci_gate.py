"""Tests for eval.ci_gate — require-zero-wrong + no-24s-regression + scramble stability.

Python 3.7+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval.oracle import BlanRow  # noqa: E402
from eval.ci_gate import gate, scramble_stability  # noqa: E402


def mk(key, result, time=1.0, match="SKIP"):
    return CaseResult(key=key, logic="QF_NIA", family="f", path="/b/" + key,
                      result=result, time=time, match=match)


class TestGate(unittest.TestCase):
    def test_passes_zero_wrong_and_no_24s_regression(self):
        cand = [mk("k1", "sat", 1.0, "MATCH"), mk("k2", "unsat", 2.0, "MATCH")]
        base = [mk("k1", "sat", 1.0, "MATCH")]
        r = gate(cand, baseline=base)
        self.assertTrue(r.passed, r.reasons)

    def test_fails_on_any_wrong(self):
        r = gate([mk("k1", "sat", 1.0, "MISMATCH")])
        self.assertFalse(r.passed)
        self.assertEqual(r.wrong, 1)

    def test_fails_on_24s_regression(self):
        cand = [mk("k1", "sat", 100.0, "MATCH")]  # solved, but slower than 24s
        base = [mk("k1", "sat", 1.0, "MATCH")]     # solved within 24s
        r = gate(cand, baseline=base)
        self.assertFalse(r.passed)
        self.assertEqual(r.solved_24_delta, -1)

    def test_blan_decided_disagreement_counts_as_wrong(self):
        cand = [mk("k1", "sat", 1.0, "SKIP")]
        blan = {"k1": BlanRow("unsat", 1.0)}
        r = gate(cand, blan_map=blan)
        self.assertFalse(r.passed)
        self.assertEqual(r.wrong, 1)


class TestScrambleStability(unittest.TestCase):
    def test_detects_verdict_flip_as_soundness_bug(self):
        uns = [mk("QF_NIA/f/k1.smt2", "sat", 1.0)]
        scr = [mk("QF_NIA/f/k1.smt2", "unsat", 1.0)]
        r = scramble_stability(uns, scr)
        self.assertFalse(r.passed)
        self.assertIn("QF_NIA/f/k1.smt2", r.flips)

    def test_stable_run_passes(self):
        uns = [mk("QF_NIA/f/k1.smt2", "sat", 1.0), mk("QF_NIA/f/k2.smt2", "unsat", 2.0)]
        scr = [mk("QF_NIA/f/k1.smt2", "sat", 1.1), mk("QF_NIA/f/k2.smt2", "unsat", 2.2)]
        r = scramble_stability(uns, scr)
        self.assertTrue(r.passed, r.reasons)
        self.assertEqual(r.flips, [])


if __name__ == "__main__":
    unittest.main()
