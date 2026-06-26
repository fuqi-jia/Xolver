#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests for diff_query.py -- named queries over diff_results.

Builds a crafted in-schema sqlite covering one row per query category, then asserts
each named query returns exactly the right keys. Also checks the --division filter,
schema-tolerance (missing audit column), and the CLI markdown shape.

    python3 tools/test_diff_query.py

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
import diff_query  # noqa: E402


def mkrow(key, division, dv, av, ov, dprefix="d"):
    row = {c: None for c in ALL_COLS}
    row.update({
        "key": key, "division": division, "file_path": "/x/" + key,
        "file_size_bytes": 10, "declared_logic": division,
        "xolver_default_verdict": dv, "xolver_default_time_ms": 5,
        "xolver_allon_verdict": av, "xolver_allon_time_ms": 4,
        "oracle_solver": "z3", "oracle_verdict": ov, "oracle_time_ms": 7,
        "panda_node": 1, "run_timestamp": "t", "xolver_git_tip": "g",
        "file_dir_prefix": dprefix, "file_name_stem": key,
    })
    row.update(derive(row))
    return row


# (key, division, default, allon, oracle, dir_prefix)
CASES = [
    ("strength",      "QF_NIA", "sat",     "sat",     "unknown", "s"),   # oracle_blind flag=1
    ("strength_us",   "QF_NIA", "unsat",   "unsat",   "timeout", "s"),   # strength + unique_unsat
    ("weak1",         "QF_UF",  "unknown", "unknown", "sat",     "clu"), # weakness clusterA
    ("weak2",         "QF_UF",  "unknown", "unknown", "unsat",   "clu"), # weakness clusterA
    ("disagree",      "QF_NIA", "unsat",   "unsat",   "sat",     "d"),   # disagreement
    ("bothunknown",   "QF_UF",  "unknown", "timeout", "unknown", "b"),   # oracle_blind query
    ("regress",       "QF_NIA", "sat",     "unknown", "sat",     "r"),   # regression
    ("recover",       "QF_NIA", "unknown", "sat",     "sat",     "v"),   # recovery
]


def build_db(path, with_inherit=True):
    conn = sqlite3.connect(path)
    schema = SCHEMA if with_inherit else SCHEMA.replace(
        ",\n\n    -- audit sentinel: source sqlite a refreshed row inherited its oracle_* from\n"
        "    -- (NULL = oracle ran fresh this batch). Set by diff_xolver_only.py.\n"
        "    oracle_inherited_from_run TEXT", "")
    cols = ALL_COLS if with_inherit else [c for c in ALL_COLS if c != "oracle_inherited_from_run"]
    conn.executescript(schema)
    sql = "INSERT INTO diff_results (%s) VALUES (%s)" % (",".join(cols), ",".join(["?"] * len(cols)))
    for c in CASES:
        row = mkrow(*c)
        conn.execute(sql, tuple(row.get(k) for k in cols))
    conn.commit()
    return conn


class TestDiffQuery(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.db = os.path.join(self.tmp, "full.sqlite")
        self.conn = build_db(self.db)

    def keys(self, name, division=None, top=None):
        cols, rows = diff_query.run_query(self.conn, name, division, top)
        ki = cols.index("key") if "key" in cols else None
        return cols, ([r[ki] for r in rows] if ki is not None else rows)

    def test_strength_catalog(self):
        _, ks = self.keys("strength_catalog")
        self.assertEqual(set(ks), {"strength", "strength_us"})

    def test_xolver_unique_unsat(self):
        _, ks = self.keys("xolver_unique_unsat")
        # only the UNSAT-with-undecided-oracle row; 'disagree' is excluded (oracle decided)
        self.assertEqual(set(ks), {"strength_us"})

    def test_weakness_clusters(self):
        cols, rows = diff_query.run_query(self.conn, "weakness_clusters")
        d = {(r[cols.index("division")], r[cols.index("file_dir_prefix")]): r[cols.index("n_unsolved")]
             for r in rows}
        self.assertEqual(d[("QF_UF", "clu")], 2)

    def test_disagreement_audit(self):
        _, ks = self.keys("disagreement_audit")
        self.assertEqual(set(ks), {"disagree"})

    def test_oracle_blind_means_both_undecided(self):
        _, ks = self.keys("oracle_blind")
        self.assertEqual(set(ks), {"bothunknown"})

    def test_regression_and_recovery(self):
        _, rg = self.keys("regression")
        _, rc = self.keys("recovery")
        self.assertEqual(set(rg), {"regress"})
        self.assertEqual(set(rc), {"recover"})

    def test_per_division_summary(self):
        cols, rows = diff_query.run_query(self.conn, "per_division_summary")
        by = {r[cols.index("division")]: r for r in rows}
        nia = by["QF_NIA"]
        self.assertEqual(nia[cols.index("total")], 5)
        self.assertEqual(nia[cols.index("unique_win")], 2)        # strength + strength_us
        self.assertEqual(nia[cols.index("disagreements")], 1)     # disagree
        self.assertEqual(nia[cols.index("regressions")], 1)
        self.assertEqual(nia[cols.index("recoveries")], 1)

    def test_division_filter(self):
        _, ks = self.keys("strength_catalog", division="QF_NIA")
        self.assertEqual(set(ks), {"strength", "strength_us"})
        _, ks2 = self.keys("strength_catalog", division="QF_UF")
        self.assertEqual(ks2, [])

    def test_schema_tolerant_missing_audit_col(self):
        # disagreement_audit references oracle_inherited_from_run; must not crash on 23-col db
        db2 = os.path.join(self.tmp, "old.sqlite")
        build_db(db2, with_inherit=False).close()
        c2 = sqlite3.connect(db2)
        try:
            cols, rows = diff_query.run_query(c2, "disagreement_audit")
        finally:
            c2.close()
        self.assertIn("oracle_inherited_from_run", cols)
        self.assertEqual(len(rows), 1)

    def test_cli_markdown_and_list(self):
        r = subprocess.run([sys.executable, os.path.join(HERE, "diff_query.py"),
                            "--db", self.db, "--query", "per_division_summary"],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(r.returncode, 0, r.stderr.decode())
        md = r.stdout.decode()
        self.assertIn("| division |", md)
        self.assertIn("|---", md)
        lst = subprocess.run([sys.executable, os.path.join(HERE, "diff_query.py"),
                              "--db", self.db, "--list-queries"], stdout=subprocess.PIPE)
        self.assertIn("strength_catalog", lst.stdout.decode())

    def tearDown(self):
        import shutil
        self.conn.close()
        shutil.rmtree(self.tmp, ignore_errors=True)


if __name__ == "__main__":
    unittest.main(verbosity=2)
