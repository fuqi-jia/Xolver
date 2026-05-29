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


class TestFlagHygiene(unittest.TestCase):
    def test_superseded_divisor_flags_fully_removed(self):
        # DIVISOR_CAP was superseded by DIVISOR_FACTOR, which was then PROMOTED to
        # default (15abfdf) and its flag dropped — neither is a lever anymore.
        self.assertNotIn("XOLVER_NIA_DIVISOR_CAP", flags.OPTIMIZATION_FLAGS)
        self.assertNotIn("XOLVER_NIA_DIVISOR_FACTOR", flags.OPTIMIZATION_FLAGS)

    def test_new_merged_levers_registered(self):
        # Capability levers added by the integration merge (98-flag live set).
        for f in ("XOLVER_NIA_EAGER_BITBLAST", "XOLVER_NIA_NORM_CACHE",
                  "XOLVER_NIA_IFACE_LIFECYCLE", "XOLVER_ARRAY_CONGR_EXT",
                  "XOLVER_EUF_PROP"):
            self.assertIn(f, flags.OPTIMIZATION_FLAGS, f)

    def test_new_levers_routed_to_their_logics(self):
        self.assertIn("XOLVER_NIA_EAGER_BITBLAST", flags.LOGIC_FLAGS["QF_NIA"])
        self.assertIn("XOLVER_EUF_PROP", flags.LOGIC_FLAGS["QF_UF"])
        self.assertIn("XOLVER_ARRAY_CONGR_EXT", flags.LOGIC_FLAGS["QF_AX"])

    def test_non_lever_flags_excluded_from_opt(self):
        # default-ON cert / dev z3-check / strategy framework / numeric cap.
        for f in ("XOLVER_NRA_LAZARD_CELL_CERT", "XOLVER_LIA_Z3_CHECK",
                  "XOLVER_STRAT_PORTFOLIO", "XOLVER_NRA_LINEARIZE_CAP"):
            self.assertNotIn(f, flags.OPTIMIZATION_FLAGS, f)

    def test_soundness_gated_disjoint_and_excluded_from_opt(self):
        self.assertTrue(flags.SOUNDNESS_GATED)
        self.assertEqual(set(flags.SOUNDNESS_GATED) & set(flags.OPTIMIZATION_FLAGS), set())
        self.assertEqual(set(flags.SOUNDNESS_GATED) & set(flags.SOUNDNESS_FLOORS), set())
        self.assertIn("XOLVER_NRA_CAC_TRUST_UNSAT", flags.SOUNDNESS_GATED)
        self.assertIn("XOLVER_ARRAY_COMB_VALIDATE_SAT", flags.SOUNDNESS_GATED)

    def test_candidate_env_never_sets_a_soundness_gated_flag(self):
        # Even if a caller passes one, candidate_env refuses it (master-controlled).
        env = flags.candidate_env(["XOLVER_NRA_CAC_TRUST_UNSAT", "XOLVER_NIA_GCD"])
        self.assertNotIn("XOLVER_NRA_CAC_TRUST_UNSAT", env)
        self.assertEqual(env.get("XOLVER_NIA_GCD"), "1")

    def test_no_diag_dump_numeric_or_disable_flags_in_opt(self):
        for f in flags.OPTIMIZATION_FLAGS:
            self.assertNotIn("_DIAG", f, f)
            self.assertNotIn("_NO_", f, f)          # disable switches
            self.assertFalse(f.endswith("_MS"), f)  # numeric budgets
            self.assertNotIn("_DUMP", f, f)


if __name__ == "__main__":
    unittest.main()
