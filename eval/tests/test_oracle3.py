"""Tests for eval.oracle3 — 3-oracle (z3 ∪ cvc5 ∪ BLAN) join + oracle-blind tagging.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.diffmodel import DiffRow, is_jiecuo  # noqa: E402
from eval.oracle import BlanRow  # noqa: E402
from eval import oracle3  # noqa: E402


def bv(v):
    return BlanRow(verdict=v, seconds=1.0)


def drow(key, baseline, candidate, oracle):
    return DiffRow(key=key, logic="QF_NIA", family="f", baseline=baseline,
                   candidate=candidate, oracle=oracle)


class TestMergeVerdict(unittest.TestCase):
    def test_any_decided_wins(self):
        self.assertEqual(oracle3.merge_verdict(["timeout", "sat", "unknown"]), "sat")

    def test_all_undecided_is_blind(self):
        self.assertEqual(oracle3.merge_verdict(["timeout", "unknown", "error"]), "blind")
        self.assertEqual(oracle3.merge_verdict([]), "blind")

    def test_conflicting_decided_is_conflict(self):
        self.assertEqual(oracle3.merge_verdict(["sat", "unsat"]), "conflict")


class TestBuildOracle3(unittest.TestCase):
    def test_blan_confirms_where_z3_blind(self):
        z3 = {"k": bv("timeout")}
        blan = {"k": bv("sat")}
        o3 = oracle3.build_oracle3(z3_map=z3, blan_map=blan)
        self.assertEqual(o3["k"], "sat")

    def test_all_blind_key(self):
        o3 = oracle3.build_oracle3(z3_map={"k": bv("timeout")}, blan_map={"k": bv("unknown")})
        self.assertEqual(o3["k"], "blind")


class TestRescore(unittest.TestCase):
    def test_blan_catches_false_unsat_z3_missed(self):
        # candidate says unsat; diff oracle (z3) timed out -> not caught. BLAN says sat.
        rows = [drow("QF_NIA/f/a.smt2", "timeout", "unsat", "timeout")]
        o3 = oracle3.build_oracle3(blan_map={"QF_NIA/f/a.smt2": bv("sat")})
        rescored = oracle3.rescore_with_oracle3(rows, o3)
        self.assertEqual(rescored[0].oracle, "sat")
        self.assertTrue(is_jiecuo(rescored[0]))   # now a confirmed false-UNSAT

    def test_keeps_diff_oracle_when_caches_blind(self):
        rows = [drow("QF_NIA/f/a.smt2", "sat", "sat", "sat")]
        rescored = oracle3.rescore_with_oracle3(rows, {"QF_NIA/f/a.smt2": "blind"})
        self.assertEqual(rescored[0].oracle, "sat")


class TestOracleBlind(unittest.TestCase):
    def test_candidate_decided_all_oracles_blind_is_cert_audit_target(self):
        rows = [
            drow("QF_NIA/f/a.smt2", "timeout", "unsat", "timeout"),  # blind + candidate decided -> target
            drow("QF_NIA/f/b.smt2", "timeout", "unsat", "sat"),      # z3 decided -> NOT blind
            drow("QF_NIA/f/c.smt2", "timeout", "timeout", "timeout"),  # candidate undecided -> not a target
        ]
        o3 = {"QF_NIA/f/a.smt2": "blind", "QF_NIA/f/c.smt2": "blind"}
        blind = oracle3.oracle_blind_keys(rows, o3)
        self.assertEqual(blind, ["QF_NIA/f/a.smt2"])


if __name__ == "__main__":
    unittest.main()
