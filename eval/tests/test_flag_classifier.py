"""Tests for eval.flag_classifier — class taxonomy + class-aware greedy promote.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import flag_classifier as fc  # noqa: E402
from eval.flags import OPTIMIZATION_FLAGS  # noqa: E402


class TestClassify(unittest.TestCase):
    def test_eager_bitblast_is_sound_sat_finder(self):
        # Master's template: validator-gated SAT-finder, can't trip the gate.
        self.assertEqual(fc.classify_flag("XOLVER_NIA_EAGER_BITBLAST"), fc.SOUND_SAT_FINDER)
        self.assertEqual(fc.classify_flag("XOLVER_NIA_LOCALSEARCH"), fc.SOUND_SAT_FINDER)
        self.assertEqual(fc.classify_flag("XOLVER_NRA_SUBTROPICAL"), fc.SOUND_SAT_FINDER)

    def test_modular_is_unsat_producer(self):
        # Modular residue reasoner can return Unsat -> needs --allon clearance.
        self.assertEqual(fc.classify_flag("XOLVER_NIA_MODULAR"), fc.UNSAT_PRODUCER)
        self.assertEqual(fc.classify_flag("XOLVER_NRA_CAC"), fc.UNSAT_PRODUCER)

    def test_norm_cache_is_sound_perf_preproc(self):
        # Pure perf cache — no decision authority.
        self.assertEqual(fc.classify_flag("XOLVER_NIA_NORM_CACHE"), fc.SOUND_PERF_PREPROC)
        self.assertEqual(fc.classify_flag("XOLVER_PP_REWRITE"), fc.SOUND_PERF_PREPROC)

    def test_unknown_flag_is_unclassified(self):
        # Default-conservative: unknown -> UNCLASSIFIED (-> treated as UNSAT_PRODUCER).
        self.assertEqual(fc.classify_flag("XOLVER_TOTALLY_NEW_FLAG"), fc.UNCLASSIFIED)


class TestCoverage(unittest.TestCase):
    def test_all_classifications_use_valid_class(self):
        for f, c in fc.FLAG_CLASS.items():
            self.assertIn(c, fc.ALL_CLASSES, "%s -> %s" % (f, c))

    def test_no_classification_for_a_non_optimization_flag(self):
        # The map should only classify flags in the OPTIMIZATION set (catching
        # stale entries when a flag is removed from the registry).
        opt = set(OPTIMIZATION_FLAGS)
        for f in fc.FLAG_CLASS:
            self.assertIn(f, opt, "stale entry in FLAG_CLASS: %s" % f)

    def test_coverage_report_runs(self):
        # Smoke: the report formats with the current registry.
        out = fc.coverage_report()
        self.assertIn("Flag-class coverage", out)
        self.assertIn(fc.SOUND_SAT_FINDER, out)


class TestDecide(unittest.TestCase):
    def _stat(self, flag, net, jiecuo=0, div="QF_NIA"):
        return fc.FlagStat(flag=flag, division=div, net=net, jiecuo=jiecuo)

    def test_jiecuo_rejects_regardless_of_class(self):
        for f in ("XOLVER_NIA_EAGER_BITBLAST",   # SOUND_SAT_FINDER
                  "XOLVER_NIA_MODULAR",           # UNSAT_PRODUCER
                  "XOLVER_NIA_NORM_CACHE",        # SOUND_PERF_PREPROC
                  "XOLVER_UNKNOWN_X"):            # UNCLASSIFIED
            d = fc.decide(self._stat(f, net=100, jiecuo=1))
            self.assertEqual(d.decision, fc.REJECT, f)
            self.assertIn("解错", d.reason)

    def test_sound_sat_finder_promotes_on_positive_net(self):
        d = fc.decide(self._stat("XOLVER_NIA_EAGER_BITBLAST", net=42))
        self.assertEqual(d.decision, fc.PROMOTE_NOW)
        self.assertIn("invariant", d.reason)

    def test_unsat_producer_requires_full_diff_clearance(self):
        # net>0 + 0 解错 -> NEEDS_FULL_DIFF (not promote_now); --allon must clear.
        d = fc.decide(self._stat("XOLVER_NIA_MODULAR", net=14))
        self.assertEqual(d.decision, fc.NEEDS_FULL_DIFF)
        self.assertIn("--allon", d.reason)

    def test_sound_perf_preproc_promotes_on_neutral_or_positive(self):
        # net >= 0 is enough — no decision authority means no soundness risk.
        d_zero = fc.decide(self._stat("XOLVER_NIA_NORM_CACHE", net=0))
        d_pos  = fc.decide(self._stat("XOLVER_NIA_NORM_CACHE", net=5))
        self.assertEqual(d_zero.decision, fc.PROMOTE_NOW)
        self.assertEqual(d_pos.decision, fc.PROMOTE_NOW)

    def test_unclassified_treated_as_unsat_producer(self):
        # Conservative — needs --allon clearance.
        d = fc.decide(self._stat("XOLVER_BRAND_NEW_FLAG", net=10))
        self.assertEqual(d.decision, fc.NEEDS_FULL_DIFF)

    def test_zero_or_negative_net_rejects(self):
        d_neg = fc.decide(self._stat("XOLVER_NIA_EAGER_BITBLAST", net=-3))
        d_zero = fc.decide(self._stat("XOLVER_NIA_MODULAR", net=0))
        self.assertEqual(d_neg.decision, fc.REJECT)
        self.assertEqual(d_zero.decision, fc.REJECT)


class TestPromoteGreedy(unittest.TestCase):
    def test_sorts_promote_first_then_needs_diff_then_reject(self):
        stats = [
            fc.FlagStat("XOLVER_NIA_MODULAR", "QF_NIA", net=14, jiecuo=0),         # NEEDS_FULL_DIFF
            fc.FlagStat("XOLVER_NIA_EAGER_BITBLAST", "QF_NIA", net=42, jiecuo=0),  # PROMOTE_NOW
            fc.FlagStat("XOLVER_NIA_GCD", "QF_NIA", net=-1, jiecuo=0),             # REJECT
            fc.FlagStat("XOLVER_NIA_LOCALSEARCH", "QF_NIA", net=5, jiecuo=2),      # REJECT(解错)
        ]
        decisions = fc.promote_greedy(stats)
        order = [d.decision for d in decisions]
        # PROMOTE_NOW first, NEEDS_FULL_DIFF next, REJECT last.
        self.assertEqual(order[0], fc.PROMOTE_NOW)
        self.assertEqual(order[1], fc.NEEDS_FULL_DIFF)
        self.assertTrue(order[2].startswith("REJECT") or order[2] == fc.REJECT)
        self.assertEqual(order[3], fc.REJECT)

    def test_format_decisions_smoke(self):
        out = fc.format_decisions([fc.decide(fc.FlagStat(
            "XOLVER_NIA_EAGER_BITBLAST", "QF_NIA", net=42, jiecuo=0))])
        self.assertIn("PROMOTE_NOW", out)
        self.assertIn("QF_NIA", out)
        self.assertIn("SOUND_SAT_FINDER", out)


if __name__ == "__main__":
    unittest.main()
