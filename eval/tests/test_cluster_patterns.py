"""Tests for eval.cluster_patterns — named cluster classification + verification.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.cluster_patterns import (  # noqa: E402
    annotate,
    classify_cluster,
    classify_clusters,
    expected_absent_patterns,
    verification_report,
)
from eval.diffscore import JiecuoCluster  # noqa: E402


def _c(division, family, flip, count, dom="SAT14"):
    return JiecuoCluster(division=division, family=family, flip=flip,
                         count=count, dominant_pattern=dom)


class TestClassifyCluster(unittest.TestCase):
    def test_stale_binary_matches_1210_verymax_signature(self):
        # The current stale-data 1210 cluster.
        c = _c("QF_NIA", "20170427-VeryMax", "sat->unsat", 1210, dom="SAT14")
        p = classify_cluster(c)
        self.assertIsNotNone(p)
        self.assertEqual(p.name, "STALE_BINARY")
        self.assertFalse(p.expected_absent_in_fresh)

    def test_large_stale_wins_over_square_contractor(self):
        # First-match-wins: a large QF_NIA sat->unsat cluster is STALE_BINARY,
        # not SQUARE_CONTRACTOR (would be wrongly named otherwise).
        c = _c("QF_NIA", "something", "sat->unsat", 1500)
        self.assertEqual(classify_cluster(c).name, "STALE_BINARY")

    def test_small_qfnia_satunsat_is_square_contractor(self):
        # Post-fix, this should not exist; if it does in fresh data the recognizer
        # tags it as SquareContractor candidate (regression signal).
        c = _c("QF_NIA", "calypto", "sat->unsat", 25)
        p = classify_cluster(c)
        self.assertIsNotNone(p)
        self.assertEqual(p.name, "SQUARE_CONTRACTOR_X2_EQ_C")
        self.assertTrue(p.expected_absent_in_fresh)

    def test_unsat_to_sat_flip_is_not_square_contractor(self):
        # SquareContractor false-UNSAT is the sat->unsat direction; the OPPOSITE
        # flip (candidate=sat when oracle=unsat) is a different bug class.
        c = _c("QF_NIA", "calypto", "unsat->sat", 25)
        self.assertIsNone(classify_cluster(c))

    def test_other_division_is_not_square_contractor(self):
        c = _c("QF_NRA", "something", "sat->unsat", 25)
        self.assertIsNone(classify_cluster(c))


class TestClassifyClusters(unittest.TestCase):
    def test_groups_by_pattern_with_unclassified_bucket(self):
        clusters = [
            _c("QF_NIA", "VeryMax", "sat->unsat", 1210),
            _c("QF_NIA", "calypto", "sat->unsat", 30),
            _c("QF_NRA", "hycomp", "unsat->sat", 5),
        ]
        groups = classify_clusters(clusters)
        self.assertEqual(len(groups["STALE_BINARY"]), 1)
        self.assertEqual(len(groups["SQUARE_CONTRACTOR_X2_EQ_C"]), 1)
        self.assertEqual(len(groups["UNCLASSIFIED"]), 1)


class TestAnnotate(unittest.TestCase):
    def test_annotates_known_cluster_and_omits_unknown(self):
        self.assertEqual(annotate(_c("QF_NIA", "VeryMax", "sat->unsat", 1210)),
                         "= STALE_BINARY")
        self.assertEqual(annotate(_c("QF_NRA", "hycomp", "unsat->sat", 5)), "")


class TestVerificationReport(unittest.TestCase):
    def test_post_fix_absent_says_verified(self):
        # Fresh data: only stale-binary cluster (already resolved), no QF_NIA sat->unsat.
        # The SquareContractor verification should say "absent — verified".
        clusters = [_c("QF_NIA", "VeryMax", "sat->unsat", 1210)]
        # That actually matches STALE_BINARY (count>=500), not SQUARE_CONTRACTOR.
        out = verification_report(clusters)
        self.assertIn("SQUARE_CONTRACTOR_X2_EQ_C", out)
        self.assertIn("verified", out)

    def test_post_fix_present_says_regression(self):
        # A small QF_NIA sat->unsat cluster would match SquareContractor; that's a
        # regression signal post-2965e21.
        clusters = [_c("QF_NIA", "calypto", "sat->unsat", 25)]
        out = verification_report(clusters)
        self.assertIn("SQUARE_CONTRACTOR_X2_EQ_C", out)
        self.assertIn("REGRESSION", out)


class TestExpectedAbsentPatterns(unittest.TestCase):
    def test_square_contractor_is_expected_absent_others_are_not(self):
        names = {p.name for p in expected_absent_patterns()}
        self.assertIn("SQUARE_CONTRACTOR_X2_EQ_C", names)
        self.assertNotIn("STALE_BINARY", names)
        self.assertNotIn("POLYHEDRAL_IMPLIED", names)


if __name__ == "__main__":
    unittest.main()
