"""Tests for eval.diffmodel.load_diff dedup-by-key best-of-both-runs merge.

Background: master's node-slicing for QF_NRA/QF_UFNIA accidentally ran the FULL
corpus on multiple nodes, so the same key shows up in two diff_*.csv files with
different verdicts (one node finished a case, the other timed out). The
competition-fair interpretation is to credit the better measurement — this is
what a single competition run would have done.

Python 3.6+ / stdlib unittest.
"""
import io
import os
import sys
import tempfile
import unittest
from contextlib import redirect_stderr

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import diffmodel  # noqa: E402


def _write_diff(path, rows):
    with open(path, "w") as f:
        f.write("key,baseline,candidate,oracle\n")
        for r in rows:
            f.write(",".join(r) + "\n")


class TestDedupBestOfBoth(unittest.TestCase):
    def test_identical_duplicate_rows_dedup_to_one(self):
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_QF_NRA_nodeA.csv")
            b = os.path.join(d, "diff_QF_NRA_nodeB.csv")
            _write_diff(a, [("QF_NRA/f/x.smt2", "timeout", "unsat", "unsat")])
            _write_diff(b, [("QF_NRA/f/x.smt2", "timeout", "unsat", "unsat")])
            rows = diffmodel.load_diff([a, b], warn=False)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].candidate, "unsat")

    def test_decided_beats_timeout_on_candidate(self):
        # The mbo_E10 case: nodeA decided 'unsat', nodeB timed out -> merged 'unsat'.
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_nodeA.csv")
            b = os.path.join(d, "diff_nodeB.csv")
            _write_diff(a, [("QF_NRA/f/x.smt2", "timeout", "unsat",   "unsat")])
            _write_diff(b, [("QF_NRA/f/x.smt2", "timeout", "timeout", "timeout")])
            rows = diffmodel.load_diff([a, b], warn=False)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].candidate, "unsat")
        self.assertEqual(rows[0].oracle,    "unsat")

    def test_decided_beats_timeout_on_oracle(self):
        # node1: cand=unsat, oracle=timeout; node2: cand=unsat, oracle=sat ->
        # merged oracle = sat (so 解错 will fire if cand stays unsat).
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_nodeA.csv")
            b = os.path.join(d, "diff_nodeB.csv")
            _write_diff(a, [("QF_NIA/f/x.smt2", "timeout", "unsat", "timeout")])
            _write_diff(b, [("QF_NIA/f/x.smt2", "timeout", "unsat", "sat")])
            rows = diffmodel.load_diff([a, b], warn=False)
        self.assertEqual(rows[0].oracle, "sat")
        self.assertTrue(diffmodel.is_jiecuo(rows[0]))

    def test_diverging_rows_warning_emitted(self):
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_nodeA.csv")
            b = os.path.join(d, "diff_nodeB.csv")
            _write_diff(a, [("QF_NRA/f/x.smt2", "timeout", "unsat",   "unsat")])
            _write_diff(b, [("QF_NRA/f/x.smt2", "timeout", "timeout", "timeout")])
            buf = io.StringIO()
            with redirect_stderr(buf):
                diffmodel.load_diff([a, b], warn=True)
            self.assertIn("dedup", buf.getvalue())
            self.assertIn("diverging", buf.getvalue())

    def test_unique_keys_across_nodes_not_affected(self):
        # The properly-partitioned QF_NIA case: no overlap, no dedup, no warn.
        with tempfile.TemporaryDirectory() as d:
            a = os.path.join(d, "diff_nodeA.csv")
            b = os.path.join(d, "diff_nodeB.csv")
            _write_diff(a, [("QF_NIA/f/a.smt2", "timeout", "unsat", "unsat")])
            _write_diff(b, [("QF_NIA/f/b.smt2", "timeout", "sat",   "sat")])
            buf = io.StringIO()
            with redirect_stderr(buf):
                rows = diffmodel.load_diff([a, b], warn=True)
        self.assertEqual(len(rows), 2)
        self.assertEqual(buf.getvalue(), "")


if __name__ == "__main__":
    unittest.main()
