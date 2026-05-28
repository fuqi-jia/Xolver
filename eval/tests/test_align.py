"""Tests for the blan_join overlap guard + aligned file-list emitter.

Python 3.6+ / stdlib unittest.
"""
import contextlib
import io
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval.oracle import BlanRow, overlap_stats, overlap_warning  # noqa: E402
from eval import blan_join  # noqa: E402


def mk(key, result, logic="QF_NIA"):
    return CaseResult(key=key, logic=logic, family="f", path="/b/" + key, result=result, time=1.0)


def bv(v):
    return BlanRow(verdict=v, seconds=1.0)


class TestOverlapStats(unittest.TestCase):
    def test_counts_joined_xolver_and_blan(self):
        cases = [mk("QF_NIA/f/a.smt2", "sat"), mk("QF_NIA/f/b.smt2", "unsat"),
                 mk("QF_NIA/f/c.smt2", "unknown"), mk("QF_NRA/f/d.smt2", "sat")]
        blan = {"QF_NIA/f/a.smt2": bv("sat"), "QF_NIA/f/b.smt2": bv("unsat"),
                "QF_NIA/f/zzz.smt2": bv("sat")}
        st = overlap_stats(cases, blan)
        self.assertEqual(st["joined"], 2)     # a, b
        self.assertEqual(st["xolver"], 3)      # only the 3 QF_NIA cases
        self.assertEqual(st["blan"], 3)
        self.assertAlmostEqual(st["ratio"], 2.0 / 3.0)

    def test_warning_fires_below_threshold(self):
        st = {"joined": 5, "xolver": 100, "blan": 6258, "ratio": 0.05}
        w = overlap_warning(st, threshold=0.10)
        self.assertIsNotNone(w)
        self.assertIn("align", w.lower())
        self.assertIn("5", w)
        self.assertIn("100", w)

    def test_no_warning_above_threshold(self):
        st = {"joined": 50, "xolver": 100, "blan": 6258, "ratio": 0.50}
        self.assertIsNone(overlap_warning(st, threshold=0.10))

    def test_warns_when_no_xolver_cases(self):
        st = overlap_stats([], {"QF_NIA/f/a.smt2": bv("sat")})
        self.assertEqual(st["xolver"], 0)
        self.assertIsNotNone(overlap_warning(st))


class TestWriteFileList(unittest.TestCase):
    def test_writes_all_keys_sorted(self):
        blan = {"QF_NIA/f/b.smt2": bv("sat"), "QF_NIA/f/a.smt2": bv("timeout")}
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "list.txt")
            n = blan_join.write_file_list(blan, p)
            lines = open(p).read().split()
        self.assertEqual(n, 2)
        self.assertEqual(lines, ["QF_NIA/f/a.smt2", "QF_NIA/f/b.smt2"])

    def test_decided_only_filters_to_sat_unsat(self):
        blan = {"QF_NIA/f/a.smt2": bv("sat"), "QF_NIA/f/b.smt2": bv("timeout"),
                "QF_NIA/f/c.smt2": bv("unsat")}
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "list.txt")
            blan_join.write_file_list(blan, p, decided_only=True)
            lines = open(p).read().split()
        self.assertEqual(lines, ["QF_NIA/f/a.smt2", "QF_NIA/f/c.smt2"])


class TestBlanJoinMainAlign(unittest.TestCase):
    def _csv(self, d):
        p = os.path.join(d, "blan_QF_NIA_node1.csv")
        with open(p, "w") as f:
            f.write("key,verdict,seconds\nQF_NIA/f/a.smt2,sat,1.0\nQF_NIA/f/b.smt2,unsat,2.0\n")
        return p

    def test_emit_file_list_needs_only_blan(self):
        with tempfile.TemporaryDirectory() as d:
            csv = self._csv(d)
            out = os.path.join(d, "aligned.txt")
            rc = blan_join.main(["--blan", csv, "--emit-file-list", out])
            self.assertEqual(rc, 0)
            self.assertEqual(sorted(open(out).read().split()),
                             ["QF_NIA/f/a.smt2", "QF_NIA/f/b.smt2"])

    def test_low_overlap_prints_loud_warning(self):
        with tempfile.TemporaryDirectory() as d:
            csv = self._csv(d)
            # Xolver run that shares NONE of BLAN's keys -> overlap 0
            sub = os.path.join(d, "QF_NIA")
            os.makedirs(sub)
            with open(os.path.join(sub, "statistics.json"), "w") as f:
                json.dump({"meta": {"logic": "QF_NIA"},
                           "results": [{"file": "/b/QF_NIA/f/zzz.smt2", "xolver_result": "sat",
                                        "xolver_time": 1.0, "compare_result": "skip",
                                        "compare_time": 0.0, "match": "SKIP"}]}, f)
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                blan_join.main(["--run-dir", d, "--blan", csv])
            out = buf.getvalue()
        self.assertIn("WARNING", out)
        self.assertIn("align", out.lower())


if __name__ == "__main__":
    unittest.main()
