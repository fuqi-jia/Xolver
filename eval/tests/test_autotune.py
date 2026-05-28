"""Tests for eval.autotune — staged flag-space search (combine + plan).

Python 3.7+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.score import Score  # noqa: E402
from eval.autotune import combine, make_run_command, stage1_plan  # noqa: E402


class TestCombine(unittest.TestCase):
    def test_selects_gainers_and_rejects_any_flag_that_adds_wrong(self):
        base = Score(total=20, solved_1200=10, wrong=0)
        per_flag = {
            "XOLVER_NIA_GCD": Score(total=20, solved_1200=12, wrong=0),     # +2  -> select
            "XOLVER_NIA_ICP": Score(total=20, solved_1200=9, wrong=0),      # -1  -> no gain
            "XOLVER_NRA_HYBRID": Score(total=20, solved_1200=15, wrong=1),  # +5 but WRONG -> reject
            "XOLVER_PP_REWRITE": Score(total=20, solved_1200=11, wrong=0),  # +1  -> select
        }
        res = combine(base, per_flag)
        self.assertEqual(set(res.selected_flags), {"XOLVER_NIA_GCD", "XOLVER_PP_REWRITE"})

    def test_wrong_adding_flag_is_marked_rejected_with_reason(self):
        base = Score(total=20, solved_1200=10, wrong=0)
        per_flag = {"XOLVER_NRA_HYBRID": Score(total=20, solved_1200=15, wrong=2)}
        res = combine(base, per_flag)
        eff = res.effects[0]
        self.assertFalse(eff.selected)
        self.assertEqual(eff.added_wrong, 2)
        self.assertIn("wrong", eff.reason.lower())

    def test_no_gain_flag_not_selected(self):
        base = Score(total=20, solved_1200=10, wrong=0)
        res = combine(base, {"XOLVER_SAT_MIN": Score(total=20, solved_1200=10, wrong=0)})
        self.assertEqual(res.selected_flags, [])


class TestMakeRunCommand(unittest.TestCase):
    def test_command_has_env_prefix_and_run_benchmark_invocation(self):
        env = {"XOLVER_NIA_GCD": "1", "XOLVER_PP_STRICT_VALIDATION": "1"}
        cmd = make_run_command(env, solver="/bin/xolver", benchmark_dir="/b",
                               logic="QF_NIA", out_dir="/o", timeout=1200, jobs=4)
        self.assertIn("XOLVER_NIA_GCD=1", cmd)
        self.assertIn("XOLVER_PP_STRICT_VALIDATION=1", cmd)
        self.assertIn("run_benchmark.py", cmd)
        self.assertIn("--logic QF_NIA", cmd)
        self.assertIn("--compare-with z3", cmd)


class TestStage1Plan(unittest.TestCase):
    def test_emits_baseline_plus_one_run_per_flag_with_floors(self):
        specs = stage1_plan("QF_NIA", ["XOLVER_NIA_GCD", "XOLVER_NIA_ICP"],
                            solver="/x", benchmark_dir="/b", out_root="/o",
                            timeout=60, jobs=2)
        labels = [s.label for s in specs]
        self.assertIn("baseline", labels)
        self.assertIn("XOLVER_NIA_GCD", labels)
        self.assertIn("XOLVER_NIA_ICP", labels)

        base = [s for s in specs if s.label == "baseline"][0]
        # baseline keeps floors ON but no test flag
        self.assertIn("XOLVER_PP_STRICT_VALIDATION=1", base.command)
        self.assertNotIn("XOLVER_NIA_GCD=1", base.command)

        gcd = [s for s in specs if s.label == "XOLVER_NIA_GCD"][0]
        self.assertIn("XOLVER_NIA_GCD=1", gcd.command)
        self.assertIn("XOLVER_PP_STRICT_VALIDATION=1", gcd.command)  # floor still on


if __name__ == "__main__":
    unittest.main()
