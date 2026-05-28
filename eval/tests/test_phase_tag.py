"""Tests for eval.phase_tag — parse vs solve phase tagging x oracle-solvability.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval import phase_tag as pt  # noqa: E402


def _case(key, result, time=1.0, oracle=""):
    parts = key.split("/")
    fam = parts[1] if len(parts) >= 3 else "root"
    return CaseResult(key=key, logic="QF_NIA", family=fam, path="/b/" + key,
                      result=result, time=time, oracle_result=oracle, match="SKIP")


class TestClassifyPhase(unittest.TestCase):
    def test_parse_only_timeout_is_parse_phase(self):
        self.assertEqual(pt.classify_phase("timeout", 10.0, "sat", 10.0), "parse")
        self.assertEqual(pt.classify_phase("killed", 10.0, "sat", 10.0), "parse")

    def test_parsed_then_solved_is_solved(self):
        self.assertEqual(pt.classify_phase("unknown", 0.1, "sat", 10.0), "solved")
        self.assertEqual(pt.classify_phase("unknown", 0.1, "unsat", 10.0), "solved")

    def test_parsed_then_failed_is_solve_phase(self):
        self.assertEqual(pt.classify_phase("unknown", 0.1, "timeout", 10.0), "solve")

    def test_time_at_budget_counts_as_parse(self):
        self.assertEqual(pt.classify_phase("unknown", 10.0, "sat", 10.0), "parse")


class TestPhaseReport(unittest.TestCase):
    def setUp(self):
        self.parse = [
            _case("QF_NIA/famA/k1.smt2", "timeout", 10.0),   # parse blowup
            _case("QF_NIA/famA/k2.smt2", "unknown", 0.1),    # parsed ok
            _case("QF_NIA/famB/k3.smt2", "unknown", 0.1),    # parsed ok
            _case("QF_NIA/famB/k4.smt2", "timeout", 10.0),   # parse, but oracle can't solve either
        ]
        self.main = [
            _case("QF_NIA/famA/k1.smt2", "timeout", 1200.0, oracle="sat"),    # solvable, dies at parse
            _case("QF_NIA/famA/k2.smt2", "timeout", 1200.0, oracle="sat"),    # solve-phase, solvable
            _case("QF_NIA/famB/k3.smt2", "sat", 5.0, oracle="sat"),           # solved
            _case("QF_NIA/famB/k4.smt2", "timeout", 1200.0, oracle="timeout"),# parse, not oracle-solvable
        ]

    def test_phase_totals(self):
        r = pt.phase_report(self.parse, self.main, parse_budget=10.0)
        self.assertEqual(r.counts["parse"], 2)   # k1, k4
        self.assertEqual(r.counts["solve"], 1)   # k2
        self.assertEqual(r.counts["solved"], 1)  # k3
        self.assertEqual(r.joined, 4)

    def test_parse_blowup_is_solvable_cases_dying_at_parse(self):
        r = pt.phase_report(self.parse, self.main, parse_budget=10.0)
        # only k1: parse-phase AND z3-decided. k4 is parse but z3 can't solve it.
        self.assertEqual(r.parse_blowup, 1)
        self.assertEqual(r.by_family_parse_blowup.get("famA"), 1)
        self.assertNotIn("famB", r.by_family_parse_blowup)

    def test_format_mentions_phases_and_blowup(self):
        out = pt.format_phase(pt.phase_report(self.parse, self.main, parse_budget=10.0))
        low = out.lower()
        for tok in ("parse", "solve", "solved", "blowup"):
            self.assertIn(tok, low)


if __name__ == "__main__":
    unittest.main()
