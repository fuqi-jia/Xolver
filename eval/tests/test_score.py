"""Tests for eval.score — the 4 SMT-COMP score tables + PAR-2.

Python 3.7+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval.score import score, score_by  # noqa: E402


def mk(result, time, match="MATCH", family="fam", logic="QF_NIA"):
    return CaseResult(key=logic + "/" + family + "/c.smt2", logic=logic, family=family,
                      path="/b/" + logic + "/" + family + "/c.smt2",
                      result=result, time=time, oracle_result="", oracle_time=0.0, match=match)


class TestScore(unittest.TestCase):
    def setUp(self):
        # main_t=1200, fast_t=24
        self.cases = [
            mk("sat", 5.0, "MATCH"),       # solved@1200, solved@24, sat
            mk("unsat", 100.0, "MATCH"),   # solved@1200, NOT@24, unsat
            mk("sat", 3.0, "MISMATCH"),    # WRONG — excluded from solved/sat
            mk("unknown", 1200.0, "DIFF"), # free unknown
            mk("timeout", 1200.0, "SKIP"), # free unknown
        ]

    def test_solved_1200_excludes_wrong_and_undecided(self):
        s = score(self.cases, main_t=1200.0, fast_t=24.0)
        self.assertEqual(s.solved_1200, 2)

    def test_24s_rescore_drops_slow_solves(self):
        s = score(self.cases, main_t=1200.0, fast_t=24.0)
        self.assertEqual(s.solved_24, 1)  # only the 5s sat

    def test_sat_unsat_split_excludes_wrong(self):
        s = score(self.cases, main_t=1200.0, fast_t=24.0)
        self.assertEqual(s.sat, 1)    # the MISMATCH sat is NOT counted
        self.assertEqual(s.unsat, 1)
        self.assertEqual(s.sat + s.unsat, s.solved_1200)

    def test_wrong_is_counted_separately(self):
        s = score(self.cases, main_t=1200.0, fast_t=24.0)
        self.assertEqual(s.wrong, 1)

    def test_unknown_and_timeout_are_free(self):
        s = score(self.cases, main_t=1200.0, fast_t=24.0)
        self.assertEqual(s.unknown, 2)  # unknown + timeout, neither solved nor wrong

    def test_total(self):
        self.assertEqual(score(self.cases).total, 5)

    def test_par2_penalizes_unsolved_and_wrong_at_2T(self):
        s = score(self.cases, main_t=1200.0, fast_t=24.0)
        # 5 + 100 + (2*1200)*3 = 7305 over 5 cases
        self.assertAlmostEqual(s.par2, 7305.0 / 5.0)


class TestScoreBy(unittest.TestCase):
    def test_groups_by_family(self):
        cases = [mk("sat", 1.0, family="AProVE"),
                 mk("unsat", 2.0, family="AProVE"),
                 mk("sat", 3.0, family="calypto")]
        by = score_by(cases, lambda c: c.family, main_t=1200.0, fast_t=24.0)
        self.assertEqual(set(by.keys()), {"AProVE", "calypto"})
        self.assertEqual(by["AProVE"].solved_1200, 2)
        self.assertEqual(by["calypto"].solved_1200, 1)


if __name__ == "__main__":
    unittest.main()
