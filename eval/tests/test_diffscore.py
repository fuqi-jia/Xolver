"""Tests for eval.diffmodel + eval.diffscore — diff scorer, 解错 gate, stale detector.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import diffmodel as dm  # noqa: E402
from eval import diffscore as ds  # noqa: E402


def row(family, baseline, candidate, oracle, name="c", logic="QF_NIA"):
    key = "%s/%s/%s.smt2" % (logic, family, name)
    return dm.DiffRow(key=key, logic=logic, family=family, baseline=baseline,
                      candidate=candidate, oracle=oracle)


class TestDiffModel(unittest.TestCase):
    def test_load_diff_parses_columns(self):
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "diff_QF_NIA_node1.csv")
            with open(p, "w") as f:
                f.write("key,baseline,candidate,oracle\n")
                f.write("QF_NIA/AProVE/a.smt2,timeout,sat,sat\n")
            rows = dm.load_diff(p)
        self.assertEqual(len(rows), 1)
        r = rows[0]
        self.assertEqual((r.logic, r.family, r.baseline, r.candidate, r.oracle),
                         ("QF_NIA", "AProVE", "timeout", "sat", "sat"))

    def test_jiecuo_requires_both_decided_and_disagree(self):
        self.assertTrue(dm.is_jiecuo(row("f", "sat", "unsat", "sat")))   # cand wrong
        self.assertFalse(dm.is_jiecuo(row("f", "sat", "sat", "sat")))    # agree
        self.assertFalse(dm.is_jiecuo(row("f", "sat", "unsat", "timeout")))  # oracle blind
        self.assertFalse(dm.is_jiecuo(row("f", "sat", "timeout", "sat")))    # cand undecided

    def test_jiecuo_flip_is_oracle_to_candidate(self):
        self.assertEqual(dm.jiecuo_flip(row("f", "sat", "unsat", "sat")), "sat->unsat")

    def test_correct_solved_excludes_contradiction(self):
        self.assertTrue(dm.correct_solved("sat", "sat"))
        self.assertTrue(dm.correct_solved("sat", "timeout"))   # decided, oracle blind
        self.assertFalse(dm.correct_solved("sat", "unsat"))    # contradicts oracle
        self.assertFalse(dm.correct_solved("timeout", "sat"))  # undecided


class TestFamilyScore(unittest.TestCase):
    def setUp(self):
        self.rows = [
            row("famA", "timeout", "sat", "sat"),    # recovered
            row("famA", "sat", "sat", "sat"),         # both solved
            row("famA", "sat", "timeout", "sat"),     # regressed
            row("famA", "sat", "unsat", "sat"),       # 解错 (+regressed)
            row("famB", "timeout", "unsat", "timeout"),  # recovered (oracle blind, no contradiction)
        ]

    def test_per_family_counts(self):
        fs = {f.family: f for f in ds.family_split(self.rows)}
        a = fs["famA"]
        self.assertEqual(a.baseline_solved, 3)
        self.assertEqual(a.candidate_solved, 2)
        self.assertEqual(a.recovered, 1)
        self.assertEqual(a.regressed, 2)
        self.assertEqual(a.jiecuo, 1)
        b = fs["famB"]
        self.assertEqual(b.candidate_solved, 1)
        self.assertEqual(b.recovered, 1)
        self.assertEqual(b.jiecuo, 0)

    def test_division_rollup_and_net_delta(self):
        dv = ds.division_rollup(self.rows)
        self.assertEqual(len(dv), 1)
        q = dv[0]
        self.assertEqual(q.division, "QF_NIA")
        self.assertEqual(q.baseline_solved, 3)
        self.assertEqual(q.candidate_solved, 3)
        self.assertEqual(q.net_delta, 0)
        self.assertEqual(q.jiecuo, 1)


class TestStaleDetector(unittest.TestCase):
    def test_clusters_jiecuo_by_family_and_flip(self):
        rows = [row("famC", "sat", "unsat", "sat", name="x%d_edge_closing_0" % i)
                for i in range(5)]   # 5 jiecuo, same family + flip
        rows.append(row("famD", "unsat", "sat", "unsat", name="y_safety_0"))  # 1 scattered, other dir
        clusters = ds.jiecuo_clusters(rows)
        top = clusters[0]
        self.assertEqual(top.family, "famC")
        self.assertEqual(top.flip, "sat->unsat")
        self.assertEqual(top.count, 5)
        self.assertEqual(top.dominant_pattern, "edge_closing")

    def test_stale_suspect_flags_big_uniform_cluster(self):
        rows = [row("famC", "sat", "unsat", "sat", name="x%d_edge_closing_0" % i)
                for i in range(20)]
        rows.append(row("famD", "unsat", "sat", "unsat", name="y_safety_0"))
        clusters = ds.jiecuo_clusters(rows)
        suspects = ds.stale_suspects(clusters, min_count=10)
        self.assertEqual([s.family for s in suspects], ["famC"])

    def test_name_category_extraction(self):
        self.assertEqual(dm.name_category("QF_NIA/f/x__p20157_safety_0.smt2"), "safety")
        self.assertEqual(dm.name_category("QF_NIA/f/y__p31845_edge_closing_0.smt2"), "edge_closing")

    def test_name_category_falls_back_to_parent_subdir(self):
        # numbered files with no category tail -> the subdir (e.g. SAT14)
        self.assertEqual(dm.name_category("QF_NIA/20170427-VeryMax/SAT14/997.smt2"), "SAT14")


if __name__ == "__main__":
    unittest.main()
