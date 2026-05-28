"""Tests for eval.modular_ladder — graded mod-2^k Xolver-vs-z3 agreement ladder.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval import modular_ladder as ml  # noqa: E402


def mk(key, xresult, zresult):
    return CaseResult(key=key, logic="QF_NIA", family="f", path="/b/" + key,
                      result=xresult, time=1.0, oracle_result=zresult, match="SKIP")


class TestAgreement(unittest.TestCase):
    def test_classifies_each_pairing(self):
        self.assertEqual(ml.agreement(mk("k", "sat", "sat")), "agree")
        self.assertEqual(ml.agreement(mk("k", "unsat", "unsat")), "agree")
        self.assertEqual(ml.agreement(mk("k", "sat", "unsat")), "disagree")
        self.assertEqual(ml.agreement(mk("k", "sat", "unknown")), "xolver_only")
        self.assertEqual(ml.agreement(mk("k", "unknown", "unsat")), "z3_only")
        self.assertEqual(ml.agreement(mk("k", "timeout", "timeout")), "both_unknown")


class TestRungExtraction(unittest.TestCase):
    def test_rung_from_key_regex(self):
        self.assertEqual(ml.rung_from_key("QF_NIA/mod16/a.smt2", r"mod(\d+)"), "16")
        self.assertIsNone(ml.rung_from_key("QF_NIA/fam/a.smt2", r"mod(\d+)"))

    def test_rung_from_constants_power_of_two_modulus(self):
        # modulus 2^8 = 256 -> rung 8
        self.assertEqual(ml.rung_from_constants("(assert (= (mod x 256) 0))"), 8)
        # mask 2^256 - 1 -> rung 256
        mask = str(2 ** 256 - 1)
        self.assertEqual(ml.rung_from_constants("(bvand x %s)" % mask), 256)

    def test_rung_from_constants_none_when_trivial(self):
        self.assertIsNone(ml.rung_from_constants("(assert (> x 0))"))


class TestLadderReport(unittest.TestCase):
    def setUp(self):
        self.cases = [
            mk("QF_NIA/mod8/a.smt2", "sat", "sat"),       # agree
            mk("QF_NIA/mod8/b.smt2", "unsat", "unsat"),   # agree
            mk("QF_NIA/mod16/c.smt2", "sat", "unknown"),  # xolver_only
            mk("QF_NIA/mod16/e.smt2", "sat", "unsat"),    # DISAGREE (soundness)
            mk("QF_NIA/mod256/d.smt2", "sat", "timeout"), # summit: xolver_only
        ]
        self.rung_fn = lambda c: ml.rung_from_key(c.key, r"mod(\d+)")

    def test_groups_and_counts_per_rung_sorted_numeric(self):
        rungs = ml.ladder_report(self.cases, self.rung_fn)
        labels = [r.rung for r in rungs]
        self.assertEqual(labels, ["8", "16", "256"])  # numeric sort, not lexical
        by = {r.rung: r for r in rungs}
        self.assertEqual(by["8"].agree, 2)
        self.assertEqual(by["8"].disagree, 0)
        self.assertEqual(by["16"].disagree, 1)
        self.assertEqual(by["16"].xolver_only, 1)
        self.assertEqual(by["256"].xolver_only, 1)
        self.assertEqual(by["256"].z3_decided, 0)  # summit beyond oracle

    def test_total_disagreements_is_the_soundness_gate(self):
        rungs = ml.ladder_report(self.cases, self.rung_fn)
        self.assertEqual(ml.total_disagreements(rungs), 1)

    def test_format_ladder_mentions_columns(self):
        rungs = ml.ladder_report(self.cases, self.rung_fn)
        out = ml.format_ladder(rungs)
        for col in ("rung", "agree", "disagree", "xolver_only", "summit"):
            self.assertIn(col, out.lower())


if __name__ == "__main__":
    unittest.main()
