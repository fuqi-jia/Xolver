"""Tests for eval.promote — per-division × flag-config promotion table.

Python 3.6+ / stdlib unittest.
"""
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import promote  # noqa: E402


def _write_diff(path, rows):
    with open(path, "w") as f:
        f.write("key,baseline,candidate,oracle\n")
        for r in rows:
            f.write(",".join(r) + "\n")


class TestPromote(unittest.TestCase):
    def test_config_net_and_promotable(self):
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_QF_NRA_A_node1.csv")
            _write_diff(a, [("QF_NRA/f/x.smt2", "timeout", "unsat", "unsat"),  # recovered
                            ("QF_NRA/f/y.smt2", "unsat", "unsat", "unsat")])    # both
            b = os.path.join(d, "diff_QF_NIA_B_node1.csv")
            _write_diff(b, [("QF_NIA/f/z.smt2", "sat", "unsat", "sat")])        # 解错
            ca = promote.score_config("A", a)
            cb = promote.score_config("B", b)
        self.assertTrue(promote.config_promotable(ca))
        self.assertFalse(promote.config_promotable(cb))
        self.assertEqual(promote.config_net(ca), 1)
        self.assertEqual(promote.config_jiecuo(cb), 1)

    def test_table_lists_configs_and_promo_column(self):
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_QF_NRA_A_node1.csv")
            _write_diff(a, [("QF_NRA/f/x.smt2", "timeout", "unsat", "unsat")])
            b = os.path.join(d, "diff_QF_NIA_B_node1.csv")
            _write_diff(b, [("QF_NIA/f/z.smt2", "sat", "unsat", "sat")])
            out = promote.promotion_table([promote.score_config("modular", a),
                                           promote.score_config("subtropical", b)])
        self.assertIn("modular", out)
        self.assertIn("subtropical", out)
        self.assertIn("解错", out)
        self.assertIn("net", out.lower())


if __name__ == "__main__":
    unittest.main()
