#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests for diff_xolver_only.py -- incremental xolver-only re-measure.

Hermetic: builds a mock baseline sqlite + a mock xolver script (deterministic verdict
by filename), runs the helper as a subprocess, and asserts schema/inheritance/flags.

    python3 tools/test_diff_xolver_only.py

Python 3.7+, stdlib unittest only.
"""

import os
import sqlite3
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from diff_ingest import SCHEMA, ALL_COLS, derive  # noqa: E402

MOCK_XOLVER = """#!/usr/bin/env bash
# args: solve <file>.  Deterministic verdict by basename; --allon flips 'recov*'.
base="$(basename "$2")"
case "$base" in
  agree_sat*) echo sat ;;
  dis*)       echo unsat ;;
  recov*)     if [ "${MOCK_ALLON:-0}" = "1" ]; then echo sat; else echo unknown; fi ;;
  *)          echo unknown ;;
esac
"""


def make_baseline(db_path, cases, bench_dir):
    """cases: list of (stem, oracle_verdict). Writes .smt2 files + a baseline sqlite."""
    conn = sqlite3.connect(db_path)
    conn.executescript(SCHEMA)
    sql = "INSERT INTO diff_results (%s) VALUES (%s)" % (
        ",".join(ALL_COLS), ",".join(["?"] * len(ALL_COLS)))
    for stem, oracle in cases:
        div = "QF_LIA"
        ddir = os.path.join(bench_dir, div, "sub")
        os.makedirs(ddir, exist_ok=True)
        fpath = os.path.join(ddir, stem + ".smt2")
        with open(fpath, "w") as fh:
            fh.write("(set-logic QF_LIA)\n(check-sat)\n")
        row = {c: None for c in ALL_COLS}
        row.update({
            "key": "%s/sub/%s.smt2" % (div, stem), "division": div, "file_path": fpath,
            "file_size_bytes": 10, "declared_logic": div,
            "xolver_default_verdict": "unknown", "xolver_default_time_ms": 1,
            "xolver_allon_verdict": "unknown", "xolver_allon_time_ms": 1,
            "oracle_solver": "z3", "oracle_verdict": oracle, "oracle_time_ms": 7,
            "panda_node": 10, "run_timestamp": "2020-01-01T00:00:00Z",
            "xolver_git_tip": "OLDTIP", "file_dir_prefix": "sub", "file_name_stem": stem,
            "oracle_inherited_from_run": None,
        })
        row.update(derive(row))
        conn.execute(sql, tuple(row.get(c) for c in ALL_COLS))
    conn.commit()
    conn.close()


class TestXolverOnly(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.bench = os.path.join(self.tmp, "bench")
        self.baseline = os.path.join(self.tmp, "baseline.sqlite")
        self.out = os.path.join(self.tmp, "out.sqlite")
        # agree: oracle sat, xolver sat -> agree
        # dis:   oracle sat, xolver unsat -> disagreement
        # recov: oracle sat, xolver default unknown / allon sat -> recovery, no disagreement
        make_baseline(self.baseline,
                      [("agree_sat", "sat"), ("dis", "sat"), ("recov", "sat")],
                      self.bench)
        self.xolver = os.path.join(self.tmp, "mock_xolver")
        with open(self.xolver, "w") as fh:
            fh.write(MOCK_XOLVER)
        os.chmod(self.xolver, 0o755)

    def _run(self, extra=None):
        cmd = [sys.executable, os.path.join(HERE, "diff_xolver_only.py"),
               "--baseline-sqlite", self.baseline,
               "--xolver", self.xolver, "--xolver-git-tip", "NEWTIP",
               "--out", self.out, "--candflags", "MOCK_ALLON=1",
               "--timeout", "10", "-j", "2"]
        if extra:
            cmd += extra
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        return r

    def _rows(self):
        conn = sqlite3.connect(self.out)
        conn.row_factory = sqlite3.Row
        rows = {r["file_name_stem"]: r for r in conn.execute("SELECT * FROM diff_results")}
        cols = [d[1] for d in conn.execute("PRAGMA table_info(diff_results)")]
        conn.close()
        return rows, cols

    def test_schema_matches_canonical(self):
        self._run()
        _, cols = self._rows()
        self.assertEqual(cols, ALL_COLS, "output schema must equal the locked diff_ingest schema")

    def test_oracle_inherited_and_tip_updated(self):
        self._run()
        rows, _ = self._rows()
        self.assertEqual(set(rows), {"agree_sat", "dis", "recov"})
        for r in rows.values():
            self.assertEqual(r["oracle_verdict"], "sat")          # inherited
            self.assertEqual(r["oracle_solver"], "z3")            # inherited
            self.assertEqual(r["oracle_time_ms"], 7)              # inherited (not re-run)
            self.assertEqual(r["oracle_inherited_from_run"], "baseline.sqlite")
            self.assertEqual(r["xolver_git_tip"], "NEWTIP")       # updated
            self.assertNotEqual(r["run_timestamp"], "2020-01-01T00:00:00Z")  # updated

    def test_fresh_xolver_verdicts(self):
        self._run()
        rows, _ = self._rows()
        self.assertEqual(rows["agree_sat"]["xolver_default_verdict"], "sat")
        self.assertEqual(rows["dis"]["xolver_default_verdict"], "unsat")
        self.assertEqual(rows["recov"]["xolver_default_verdict"], "unknown")
        # --allon (MOCK_ALLON=1) flips recov -> sat
        self.assertEqual(rows["recov"]["xolver_allon_verdict"], "sat")

    def test_derived_flags_recomputed(self):
        self._run()
        rows, _ = self._rows()
        # disagreement: xolver unsat vs inherited oracle sat -> the soundness-audit basis
        self.assertEqual(rows["dis"]["is_disagreement"], 1)
        self.assertEqual(rows["agree_sat"]["is_disagreement"], 0)
        self.assertEqual(rows["recov"]["is_disagreement"], 0)
        # recovery: allon decided, default not
        self.assertEqual(rows["recov"]["is_recovery"], 1)
        self.assertEqual(rows["dis"]["is_recovery"], 0)

    def test_panda_filter_excludes(self):
        # node 10 is the only node; filtering to 99 must yield an empty db
        self._run(extra=["--panda-list", "99"])
        rows, _ = self._rows()
        self.assertEqual(len(rows), 0)

    def tearDown(self):
        import shutil
        shutil.rmtree(self.tmp, ignore_errors=True)


if __name__ == "__main__":
    unittest.main(verbosity=2)
