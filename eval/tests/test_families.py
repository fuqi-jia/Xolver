"""Tests for eval.families — family-level train/val split.

The split must keep each family wholly in train or wholly in val so the val set
contains families absent from train (no overfit). Deterministic given a seed.

Python 3.7+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval.families import split_families, families_by_logic  # noqa: E402


def mk(logic, family, i=0):
    key = "%s/%s/c%d.smt2" % (logic, family, i)
    return CaseResult(key=key, logic=logic, family=family, path="/b/" + key,
                      result="sat", time=1.0)


def _four_family_logic():
    return [mk("QF_NIA", f, i) for f in ("a", "b", "c", "d") for i in range(2)]


class TestSplitFamilies(unittest.TestCase):
    def test_train_and_val_families_are_disjoint(self):
        cases = _four_family_logic()
        train, val = split_families(cases, val_fraction=0.5, seed=1)
        tf = {c.family for c in train}
        vf = {c.family for c in val}
        self.assertEqual(tf & vf, set())
        self.assertEqual(tf | vf, {"a", "b", "c", "d"})
        self.assertTrue(tf and vf)

    def test_deterministic_for_same_seed(self):
        cases = _four_family_logic()
        _, v1 = split_families(cases, 0.5, seed=7)
        _, v2 = split_families(cases, 0.5, seed=7)
        self.assertEqual({c.key for c in v1}, {c.key for c in v2})

    def test_partition_is_complete_and_disjoint(self):
        cases = _four_family_logic()
        train, val = split_families(cases, 0.5, seed=3)
        self.assertEqual(len(train) + len(val), len(cases))
        keys = {c.key for c in train} | {c.key for c in val}
        self.assertEqual(len(keys), len(cases))

    def test_each_logic_split_independently(self):
        cases = [mk("QF_NIA", "a"), mk("QF_NIA", "b"),
                 mk("QF_NRA", "x"), mk("QF_NRA", "y")]
        train, val = split_families(cases, 0.5, seed=2)
        tp = {(c.logic, c.family) for c in train}
        vp = {(c.logic, c.family) for c in val}
        self.assertEqual(tp & vp, set())
        self.assertEqual({c.logic for c in val}, {"QF_NIA", "QF_NRA"})

    def test_single_family_logic_goes_all_to_train(self):
        cases = [mk("QF_NIA", "only", 0), mk("QF_NIA", "only", 1)]
        train, val = split_families(cases, 0.5, seed=1)
        self.assertEqual(len(val), 0)
        self.assertEqual(len(train), 2)


class TestFamiliesByLogic(unittest.TestCase):
    def test_collects_distinct_families_per_logic(self):
        cases = _four_family_logic() + [mk("QF_NRA", "z")]
        fbl = families_by_logic(cases)
        self.assertEqual(fbl["QF_NIA"], {"a", "b", "c", "d"})
        self.assertEqual(fbl["QF_NRA"], {"z"})


if __name__ == "__main__":
    unittest.main()
