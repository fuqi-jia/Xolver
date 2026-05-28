"""Tests for eval.loader — read run_benchmark.py statistics.json into CaseResult.

Fixtures are built in-process (tempfile) mirroring run_benchmark.py's schema, so
no fixture files are committed. Python 3.7+ / stdlib unittest.
"""
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from eval.model import CaseResult  # noqa: E402
from eval.loader import load_statistics_json, load_run_dir  # noqa: E402


def _row(path, xr, xt, cr="skip", ct=0.0, match="SKIP"):
    return {"file": path, "xolver_result": xr, "xolver_time": xt,
            "compare_result": cr, "compare_time": ct, "match": match, "note": ""}


def _stats(logic, rows):
    return {"meta": {"date": "2026-05-28T00:00:00", "logic": logic},
            "statistics": {"logic": logic, "total_files": len(rows)},
            "results": rows}


def _write_stats(dir_path, logic, rows):
    os.makedirs(dir_path, exist_ok=True)
    p = os.path.join(dir_path, "statistics.json")
    with open(p, "w") as f:
        json.dump(_stats(logic, rows), f)
    return p


class TestLoadStatisticsJson(unittest.TestCase):
    def test_parses_row_into_caseresult(self):
        with tempfile.TemporaryDirectory() as d:
            p = _write_stats(d, "QF_NIA",
                             [_row("/b/QF_NIA/AProVE/a.smt2", "sat", 1.5, "sat", 0.4, "MATCH")])
            cases = load_statistics_json(p)
        self.assertEqual(len(cases), 1)
        c = cases[0]
        self.assertIsInstance(c, CaseResult)
        self.assertEqual(c.key, "QF_NIA/AProVE/a.smt2")
        self.assertEqual(c.logic, "QF_NIA")
        self.assertEqual(c.family, "AProVE")
        self.assertEqual(c.result, "sat")
        self.assertAlmostEqual(c.time, 1.5)
        self.assertEqual(c.oracle_result, "sat")
        self.assertAlmostEqual(c.oracle_time, 0.4)
        self.assertEqual(c.match, "MATCH")

    def test_no_oracle_keeps_skip(self):
        with tempfile.TemporaryDirectory() as d:
            p = _write_stats(d, "QF_NIA", [_row("/b/QF_NIA/calypto/x.smt2", "unsat", 2.0)])
            cases = load_statistics_json(p)
        self.assertEqual(cases[0].oracle_result, "skip")
        self.assertEqual(cases[0].family, "calypto")


class TestLoadRunDir(unittest.TestCase):
    def test_loads_every_logic_subdir(self):
        with tempfile.TemporaryDirectory() as d:
            _write_stats(os.path.join(d, "QF_NIA"), "QF_NIA",
                         [_row("/b/QF_NIA/AProVE/x.smt2", "sat", 1.0)])
            _write_stats(os.path.join(d, "QF_NRA"), "QF_NRA",
                         [_row("/b/QF_NRA/meti/y.smt2", "unsat", 3.0)])
            cases = load_run_dir(d)
        self.assertEqual(len(cases), 2)
        self.assertEqual(sorted({c.logic for c in cases}), ["QF_NIA", "QF_NRA"])


if __name__ == "__main__":
    unittest.main()
