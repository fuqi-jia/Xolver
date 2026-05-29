"""Tests for eval.make_diff — join baseline+candidate runs with the cached oracle.

Python 3.6+ / stdlib unittest.
"""
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval import make_diff  # noqa: E402


def _write_run(d, logic, rows):
    sub = os.path.join(d, logic)
    os.makedirs(sub, exist_ok=True)
    results = [{"file": "/b/%s" % k, "xolver_result": v, "xolver_time": 1.0,
                "compare_result": "skip", "compare_time": 0.0, "match": "SKIP"}
               for k, v in rows]
    with open(os.path.join(sub, "statistics.json"), "w") as f:
        json.dump({"meta": {"logic": logic}, "results": results}, f)


def _write_cache(path, rows):
    with open(path, "w") as f:
        f.write("key,verdict,seconds\n")
        for k, v in rows:
            f.write("%s,%s,1.0\n" % (k, v))


class TestMakeDiff(unittest.TestCase):
    def test_joins_baseline_candidate_oracle_by_key(self):
        with tempfile.TemporaryDirectory() as d:
            base = os.path.join(d, "base")
            cand = os.path.join(d, "cand")
            _write_run(base, "QF_NIA", [("QF_NIA/f/a.smt2", "timeout"),
                                        ("QF_NIA/f/b.smt2", "sat")])
            _write_run(cand, "QF_NIA", [("QF_NIA/f/a.smt2", "unsat"),
                                        ("QF_NIA/f/b.smt2", "sat")])
            z3 = os.path.join(d, "z3.csv")
            _write_cache(z3, [("QF_NIA/f/a.smt2", "sat"), ("QF_NIA/f/b.smt2", "sat")])
            rows = make_diff.make_diff_rows(base, cand, z3)
        rows = sorted(rows)
        self.assertEqual(rows[0], ("QF_NIA/f/a.smt2", "timeout", "unsat", "sat"))
        self.assertEqual(rows[1], ("QF_NIA/f/b.smt2", "sat", "sat", "sat"))

    def test_missing_oracle_key_is_missing(self):
        with tempfile.TemporaryDirectory() as d:
            base = os.path.join(d, "base")
            cand = os.path.join(d, "cand")
            _write_run(base, "QF_NIA", [("QF_NIA/f/x.smt2", "sat")])
            _write_run(cand, "QF_NIA", [("QF_NIA/f/x.smt2", "sat")])
            z3 = os.path.join(d, "z3.csv")
            _write_cache(z3, [])  # no oracle row for x
            rows = make_diff.make_diff_rows(base, cand, z3)
        self.assertEqual(rows[0], ("QF_NIA/f/x.smt2", "sat", "sat", "missing"))

    def test_write_diff_emits_header_and_rows(self):
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "diff.csv")
            n = make_diff.write_diff([("QF_NIA/f/a.smt2", "timeout", "unsat", "sat")], out)
            text = open(out).read().splitlines()
        self.assertEqual(n, 1)
        self.assertEqual(text[0], "key,baseline,candidate,oracle")
        self.assertEqual(text[1], "QF_NIA/f/a.smt2,timeout,unsat,sat")


if __name__ == "__main__":
    unittest.main()
