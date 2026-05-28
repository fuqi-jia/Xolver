"""Tests for eval.model — CaseResult + key/family normalization.

Python 3.7+ / stdlib unittest only (test server may lack 3.12; see memory
feedback_python_version_conservative).
"""
import os
import sys
import unittest

# Make the repo root importable so `import eval.model` works when run as
# `python3 -m unittest` from anywhere.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import normalize_key, family_of  # noqa: E402


class TestNormalizeKey(unittest.TestCase):
    def test_canonical_absolute_path(self):
        p = "/home/u/proj/benchmark/non-incremental/QF_NIA/AProVE/foo.smt2"
        self.assertEqual(normalize_key(p, "QF_NIA"), "QF_NIA/AProVE/foo.smt2")

    def test_keys_off_last_marker_occurrence(self):
        # Mirrors BLAN's `${f##*QF_NIA/}`: strip longest prefix ending QF_NIA/.
        p = "/data/QF_NIA_mirror/x/QF_NIA/calypto/bar.smt2"
        self.assertEqual(normalize_key(p, "QF_NIA"), "QF_NIA/calypto/bar.smt2")

    def test_nested_family_subdirs_preserved(self):
        p = "/b/QF_NIA/AProVE/sub/deep/baz.smt2"
        self.assertEqual(normalize_key(p, "QF_NIA"), "QF_NIA/AProVE/sub/deep/baz.smt2")

    def test_missing_marker_returns_none(self):
        self.assertIsNone(normalize_key("/b/QF_LIA/fam/x.smt2", "QF_NIA"))

    def test_already_normalized_key_is_idempotent(self):
        self.assertEqual(normalize_key("QF_NIA/AProVE/foo.smt2", "QF_NIA"),
                         "QF_NIA/AProVE/foo.smt2")


class TestFamilyOf(unittest.TestCase):
    def test_first_component_after_logic_is_family(self):
        self.assertEqual(family_of("QF_NIA/AProVE/foo.smt2", "QF_NIA"), "AProVE")

    def test_family_is_top_dir_not_leaf_dir(self):
        self.assertEqual(family_of("QF_NIA/AProVE/sub/deep/baz.smt2", "QF_NIA"), "AProVE")

    def test_file_directly_under_logic_is_root_family(self):
        self.assertEqual(family_of("QF_NIA/foo.smt2", "QF_NIA"), "root")


if __name__ == "__main__":
    unittest.main()
