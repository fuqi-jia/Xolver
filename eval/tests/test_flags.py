"""Tests for eval.flags — the XOLVER_* flag registry + candidate env builder.

Python 3.7+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import flags  # noqa: E402


class TestFlagRegistry(unittest.TestCase):
    def test_optimization_and_floor_flags_are_disjoint(self):
        self.assertEqual(set(flags.OPTIMIZATION_FLAGS) & set(flags.SOUNDNESS_FLOORS), set())

    def test_registries_nonempty_and_well_formed(self):
        self.assertTrue(flags.OPTIMIZATION_FLAGS)
        self.assertTrue(flags.SOUNDNESS_FLOORS)
        for f in list(flags.OPTIMIZATION_FLAGS) + list(flags.SOUNDNESS_FLOORS):
            self.assertTrue(f.startswith("XOLVER_"), f)


class TestCandidateEnv(unittest.TestCase):
    def test_floors_pinned_on_even_with_no_selected_flags(self):
        env = flags.candidate_env([])
        for floor in flags.SOUNDNESS_FLOORS:
            self.assertEqual(env.get(floor), "1", floor)

    def test_selected_flags_turned_on(self):
        env = flags.candidate_env(["XOLVER_NIA_GCD", "XOLVER_NIA_ICP"])
        self.assertEqual(env["XOLVER_NIA_GCD"], "1")
        self.assertEqual(env["XOLVER_NIA_ICP"], "1")
        # floors still present
        for floor in flags.SOUNDNESS_FLOORS:
            self.assertEqual(env.get(floor), "1")

    def test_floors_cannot_be_dropped_by_selection(self):
        # Even if a caller tries to select nothing, floors remain — the search
        # can never produce an unsound (floor-off) candidate.
        env = flags.candidate_env([])
        self.assertTrue(set(flags.SOUNDNESS_FLOORS).issubset(set(env.keys())))


class TestLogicFlags(unittest.TestCase):
    def test_logic_flags_are_subset_of_optimization_flags(self):
        opt = set(flags.OPTIMIZATION_FLAGS)
        for logic, fl in flags.LOGIC_FLAGS.items():
            self.assertTrue(set(fl).issubset(opt), "%s: %s" % (logic, set(fl) - opt))

    def test_nia_logic_has_nia_flags(self):
        self.assertIn("XOLVER_NIA_GCD", flags.LOGIC_FLAGS["QF_NIA"])


if __name__ == "__main__":
    unittest.main()
