"""Tests for eval.analyze and eval.blan_join CLIs (pure helpers + main smoke).

Python 3.7+ / stdlib unittest.
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
from eval import analyze, blan_join  # noqa: E402


def mk(logic, family, result, time, match="MATCH"):
    key = "%s/%s/c.smt2" % (logic, family)
    return CaseResult(key=key, logic=logic, family=family, path="/b/" + key,
                      result=result, time=time, match=match)


def _write_run(d, logic, rows):
    sub = os.path.join(d, logic)
    os.makedirs(sub, exist_ok=True)
    data = {"meta": {"logic": logic}, "statistics": {"logic": logic},
            "results": rows}
    with open(os.path.join(sub, "statistics.json"), "w") as f:
        json.dump(data, f)


def _row(path, xr, xt, match="SKIP", cr="skip"):
    return {"file": path, "xolver_result": xr, "xolver_time": xt,
            "compare_result": cr, "compare_time": 0.0, "match": match, "note": ""}


class TestAnalyzeHelpers(unittest.TestCase):
    def test_build_report_groups_by_logic(self):
        cases = [mk("QF_NIA", "a", "sat", 1.0), mk("QF_NRA", "b", "unsat", 2.0)]
        rep = analyze.build_report(cases, group_by="logic")
        self.assertEqual(set(rep.groups.keys()), {"QF_NIA", "QF_NRA"})
        self.assertEqual(rep.overall.solved_1200, 2)

    def test_timeout_bucket_boundaries(self):
        self.assertEqual(analyze.timeout_bucket(0.5), "<1s")
        self.assertEqual(analyze.timeout_bucket(10.0), "1-24s")
        self.assertEqual(analyze.timeout_bucket(100.0), "24-300s")
        self.assertEqual(analyze.timeout_bucket(800.0), "300-1200s")
        self.assertEqual(analyze.timeout_bucket(1200.0), "1200s+")

    def test_format_report_shows_the_four_tables(self):
        cases = [mk("QF_NIA", "a", "sat", 1.0)]
        out = analyze.format_report(analyze.build_report(cases, group_by="logic"))
        for col in ("solved@1200", "solved@24", "sat", "unsat", "wrong", "PAR2"):
            self.assertIn(col, out)


class TestAnalyzeMain(unittest.TestCase):
    def test_main_on_run_dir_exits_zero(self):
        with tempfile.TemporaryDirectory() as d:
            _write_run(d, "QF_NIA", [_row("/b/QF_NIA/a/x.smt2", "sat", 1.0)])
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = analyze.main(["--run-dir", d, "--by", "logic"])
        self.assertEqual(rc, 0)
        self.assertIn("solved@1200", buf.getvalue())


class TestBlanJoinMain(unittest.TestCase):
    def test_main_reports_decided_disagreement(self):
        with tempfile.TemporaryDirectory() as d:
            # Xolver says sat, BLAN says unsat -> decided disagreement
            _write_run(d, "QF_NIA", [_row("/b/QF_NIA/f/k.smt2", "sat", 1.0)])
            csvp = os.path.join(d, "blan_QF_NIA_node1.csv")
            with open(csvp, "w") as f:
                f.write("key,verdict,seconds\nQF_NIA/f/k.smt2,unsat,2.0\n")
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = blan_join.main(["--run-dir", d, "--blan", csvp])
        out = buf.getvalue()
        self.assertIn("QF_NIA/f/k.smt2", out)
        self.assertIn("DISAGREE", out.upper())
        # nonzero exit signals a soundness disagreement was found
        self.assertNotEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
