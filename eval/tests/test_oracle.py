"""Tests for eval.oracle — BLAN CSV load + 3-oracle differential.

Python 3.7+ / stdlib unittest. BLAN CSV fixtures written in-process.
"""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval.oracle import (  # noqa: E402
    BlanRow, load_blan_csv, decided_disagreements, blan_debug_targets,
)


def mk(key, result, match="SKIP", logic="QF_NIA", oracle_result="skip"):
    parts = key.split("/")
    fam = parts[1] if len(parts) >= 3 else "root"
    return CaseResult(key=key, logic=logic, family=fam, path="/b/" + key,
                      result=result, time=1.0, oracle_result=oracle_result,
                      oracle_time=0.0, match=match)


def _bv(verdict, seconds):
    return BlanRow(verdict=verdict, seconds=seconds)


def _write_csv(path, rows):
    with open(path, "w") as f:
        f.write("key,verdict,seconds\n")
        for k, v, s in rows:
            f.write("%s,%s,%s\n" % (k, v, s))


class TestLoadBlanCsv(unittest.TestCase):
    def test_parses_rows(self):
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "blan_QF_NIA_node1.csv")
            _write_csv(p, [("QF_NIA/AProVE/a.smt2", "sat", "1.2"),
                           ("QF_NIA/calypto/b.smt2", "unsat", "3.4")])
            m = load_blan_csv(p)
        self.assertEqual(m["QF_NIA/AProVE/a.smt2"].verdict, "sat")
        self.assertAlmostEqual(m["QF_NIA/AProVE/a.smt2"].seconds, 1.2)
        self.assertEqual(m["QF_NIA/calypto/b.smt2"].verdict, "unsat")

    def test_merges_multiple_node_csvs(self):
        with tempfile.TemporaryDirectory() as d:
            p1 = os.path.join(d, "blan_QF_NIA_node1.csv")
            p2 = os.path.join(d, "blan_QF_NIA_node2.csv")
            _write_csv(p1, [("QF_NIA/f/a.smt2", "sat", "1.0")])
            _write_csv(p2, [("QF_NIA/f/b.smt2", "unsat", "2.0")])
            m = load_blan_csv([p1, p2])
        self.assertEqual(set(m.keys()), {"QF_NIA/f/a.smt2", "QF_NIA/f/b.smt2"})

    def test_dedup_prefers_decided_verdict(self):
        with tempfile.TemporaryDirectory() as d:
            p1 = os.path.join(d, "node1.csv")
            p2 = os.path.join(d, "node2.csv")
            _write_csv(p1, [("QF_NIA/f/a.smt2", "timeout", "1200")])
            _write_csv(p2, [("QF_NIA/f/a.smt2", "sat", "5.0")])
            m = load_blan_csv([p1, p2])
        self.assertEqual(m["QF_NIA/f/a.smt2"].verdict, "sat")


class TestDecidedDisagreements(unittest.TestCase):
    def setUp(self):
        self.cases = [
            mk("QF_NIA/f/k1.smt2", "sat"),       # blan unsat -> DISAGREE
            mk("QF_NIA/f/k2.smt2", "sat"),       # blan sat   -> agree
            mk("QF_NIA/f/k3.smt2", "unknown"),   # blan unsat -> debug target, not disagree
            mk("QF_NIA/f/k4.smt2", "unsat"),     # blan timeout -> blan undecided, skip
        ]
        self.blan = {
            "QF_NIA/f/k1.smt2": _bv("unsat", 1.0),
            "QF_NIA/f/k2.smt2": _bv("sat", 1.0),
            "QF_NIA/f/k3.smt2": _bv("unsat", 1.0),
            "QF_NIA/f/k4.smt2": _bv("timeout", 1200.0),
        }

    def test_blan_disagreement_requires_both_decided_and_differ(self):
        dis = decided_disagreements(self.cases, blan_map=self.blan)
        keys = {d.key for d in dis}
        self.assertIn("QF_NIA/f/k1.smt2", keys)
        self.assertNotIn("QF_NIA/f/k2.smt2", keys)
        self.assertNotIn("QF_NIA/f/k3.smt2", keys)
        self.assertNotIn("QF_NIA/f/k4.smt2", keys)
        k1 = [d for d in dis if d.key == "QF_NIA/f/k1.smt2"][0]
        self.assertEqual(k1.oracle, "BLAN")
        self.assertEqual(k1.xolver_result, "sat")
        self.assertEqual(k1.oracle_result, "unsat")

    def test_z3_mismatch_is_a_disagreement(self):
        cases = [mk("QF_NIA/f/m.smt2", "sat", match="MISMATCH", oracle_result="unsat")]
        dis = decided_disagreements(cases, oracle_label="z3")
        self.assertEqual(len(dis), 1)
        self.assertEqual(dis[0].oracle, "z3")

    def test_debug_targets_are_blan_decided_xolver_undecided(self):
        targets = blan_debug_targets(self.cases, self.blan)
        keys = {t.key for t in targets}
        self.assertIn("QF_NIA/f/k3.smt2", keys)
        self.assertNotIn("QF_NIA/f/k1.smt2", keys)
        self.assertNotIn("QF_NIA/f/k4.smt2", keys)  # blan undecided


if __name__ == "__main__":
    unittest.main()
