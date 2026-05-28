"""Tests for eval.compare — baseline-vs-candidate solved-delta diff + promotion gate.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval import compare  # noqa: E402


def mk(family, result, time, match="MATCH", oracle_result="", logic="QF_NIA"):
    key = "%s/%s/c.smt2" % (logic, family)
    return CaseResult(key=key, logic=logic, family=family, path="/b/" + key,
                      result=result, time=time, oracle_result=oracle_result, match=match)


class TestCompareRuns(unittest.TestCase):
    def test_positive_solved_delta_promotes(self):
        base = [mk("famA", "sat", 1.0), mk("famB", "timeout", 10.0)]
        cand = [mk("famA", "sat", 1.0), mk("famB", "sat", 5.0)]  # famB recovered
        res = compare.compare_runs(base, cand, group_by="family")
        self.assertEqual(res.overall.d_solved_1200, 1)
        self.assertTrue(res.promote)
        # family-split: famB shows the +1
        byg = {g.group: g for g in res.groups}
        self.assertEqual(byg["QF_NIA/famB"].d_solved_1200, 1)

    def test_added_wrong_blocks_promotion_even_with_solve_gain(self):
        base = [mk("famA", "sat", 1.0), mk("famB", "timeout", 10.0)]
        # famB "recovered" but it's actually a MISMATCH (decided-disagreement)
        cand = [mk("famA", "sat", 1.0),
                mk("famB", "sat", 5.0, match="MISMATCH", oracle_result="unsat")]
        res = compare.compare_runs(base, cand, group_by="family")
        self.assertGreaterEqual(res.decided_disagreements, 1)
        self.assertFalse(res.promote)

    def test_zero_solve_gain_does_not_promote(self):
        base = [mk("famA", "sat", 1.0), mk("famB", "timeout", 10.0)]
        cand = [mk("famA", "sat", 1.0), mk("famB", "timeout", 10.0)]  # identical
        res = compare.compare_runs(base, cand, group_by="family")
        self.assertEqual(res.overall.d_solved_1200, 0)
        self.assertFalse(res.promote)

    def test_solved24_gain_promotes_even_if_1200_flat(self):
        # same solved@1200, but candidate solves one within 24s that baseline didn't
        base = [mk("famA", "sat", 100.0)]   # solved@1200 but not @24
        cand = [mk("famA", "sat", 5.0)]     # now solved @24
        res = compare.compare_runs(base, cand, group_by="family")
        self.assertEqual(res.overall.d_solved_1200, 0)
        self.assertEqual(res.overall.d_solved_24, 1)
        self.assertTrue(res.promote)

    def test_format_has_delta_columns_and_verdict(self):
        base = [mk("famA", "sat", 1.0)]
        cand = [mk("famA", "sat", 1.0)]
        out = compare.format_compare(compare.compare_runs(base, cand, group_by="family"))
        self.assertIn("d_solved", out.lower())
        self.assertIn("promote", out.lower())


if __name__ == "__main__":
    unittest.main()
