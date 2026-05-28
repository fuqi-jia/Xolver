"""Tests for eval.select — family-split train/val file-list generator.

Builds a temp benchmark tree (empty .smt2 files). Python 3.6+ / stdlib unittest.
"""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import select  # noqa: E402


def _tree(root, logic="QF_TEST"):
    """famA: 3 files, famB: 2, famC: 1, famD: 1 -> 4 families, 7 files."""
    spec = {"famA": 3, "famB": 2, "famC": 1, "famD": 1}
    for fam, n in spec.items():
        d = os.path.join(root, logic, fam)
        os.makedirs(d, exist_ok=True)
        for i in range(n):
            open(os.path.join(d, "c%d.smt2" % i), "w").close()
    return logic


class TestEnumerate(unittest.TestCase):
    def test_keys_and_families(self):
        with tempfile.TemporaryDirectory() as d:
            logic = _tree(d)
            cases = select.enumerate_cases(logic, d)
        self.assertEqual(len(cases), 7)
        self.assertTrue(all(c.key.startswith("QF_TEST/") for c in cases))
        self.assertEqual({c.family for c in cases}, {"famA", "famB", "famC", "famD"})


class TestSelect(unittest.TestCase):
    def test_train_val_families_disjoint(self):
        with tempfile.TemporaryDirectory() as d:
            logic = _tree(d)
            train, val = select.select_cases(logic, d, val_fraction=0.5, seed=1)
        tf = {c.family for c in train}
        vf = {c.family for c in val}
        self.assertEqual(tf & vf, set())
        self.assertEqual(tf | vf, {"famA", "famB", "famC", "famD"})
        self.assertTrue(tf and vf)
        self.assertEqual(len(train) + len(val), 7)

    def test_per_family_cap_limits_files(self):
        with tempfile.TemporaryDirectory() as d:
            logic = _tree(d)
            train, val = select.select_cases(logic, d, val_fraction=0.5, seed=1,
                                             per_family_cap=1)
        # every family in either side contributes at most 1 file
        from collections import Counter
        for side in (train, val):
            counts = Counter(c.family for c in side)
            self.assertTrue(all(v <= 1 for v in counts.values()), counts)

    def test_deterministic(self):
        with tempfile.TemporaryDirectory() as d:
            logic = _tree(d)
            t1, v1 = select.select_cases(logic, d, val_fraction=0.5, seed=5, per_family_cap=1)
            t2, v2 = select.select_cases(logic, d, val_fraction=0.5, seed=5, per_family_cap=1)
        self.assertEqual([c.key for c in t1], [c.key for c in t2])
        self.assertEqual([c.key for c in v1], [c.key for c in v2])


class TestWriteAndMain(unittest.TestCase):
    def test_main_writes_train_and_val_lists(self):
        with tempfile.TemporaryDirectory() as d:
            logic = _tree(d)
            tr = os.path.join(d, "train.txt")
            va = os.path.join(d, "val.txt")
            rc = select.main(["--logic", logic, "--benchmark-dir", d,
                              "--val-fraction", "0.5", "--seed", "1",
                              "--out-train", tr, "--out-val", va])
            self.assertEqual(rc, 0)
            train_keys = open(tr).read().split()
            val_keys = open(va).read().split()
        self.assertTrue(train_keys and val_keys)
        # disjoint + all under the logic + total == 7
        self.assertEqual(set(train_keys) & set(val_keys), set())
        self.assertTrue(all(k.startswith("QF_TEST/") for k in train_keys + val_keys))
        self.assertEqual(len(train_keys) + len(val_keys), 7)


if __name__ == "__main__":
    unittest.main()
