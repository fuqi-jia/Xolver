#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""diff_merge.py -- merge per-node SQLite dbs into one results/<date>/full.sqlite.

Each panda node emits panda<N>_<ts>.sqlite (via diff_ingest.py). Master collects
them and runs:

    python3 diff_merge.py --out results/2026-06-XX/full.sqlite panda*_*.sqlite

Rows are keyed on `key` (PRIMARY KEY = LOGIC/sub/file.smt2), which is unique across
nodes (each node owns a disjoint slice of a division), so the union is a clean dedup.

Equivalent ad-hoc sqlite3 one-liner (no python):
    sqlite3 full.sqlite < /dev/null   # create empty
    for db in panda*_*.sqlite; do
      sqlite3 full.sqlite "ATTACH '$db' AS s; \\
        INSERT OR REPLACE INTO diff_results SELECT * FROM s.diff_results; DETACH s;"
    done

Python 3.7+, stdlib only.
"""

import argparse
import os
import sqlite3
import sys

# Reuse the canonical schema from diff_ingest if importable; else inline a copy.
try:
    from diff_ingest import SCHEMA  # type: ignore
except Exception:  # pragma: no cover - import fallback
    SCHEMA = None


def schema_from(db_path):
    """Pull the CREATE statements from an existing node db when SCHEMA isn't importable."""
    conn = sqlite3.connect(db_path)
    try:
        rows = conn.execute(
            "SELECT sql FROM sqlite_master WHERE sql IS NOT NULL "
            "AND (type='table' OR type='index') AND name LIKE '%diff_results%' "
            "OR (type='index')"
        ).fetchall()
        stmts = [r[0] for r in rows if r[0]]
        # also grab the table itself
        t = conn.execute(
            "SELECT sql FROM sqlite_master WHERE type='table' AND name='diff_results'"
        ).fetchone()
        if t and t[0] not in stmts:
            stmts.insert(0, t[0])
        return ";\n".join(stmts) + ";"
    finally:
        conn.close()


def main():
    ap = argparse.ArgumentParser(description="Merge per-node diff sqlite dbs.")
    ap.add_argument("--out", required=True, help="output merged sqlite path")
    ap.add_argument("dbs", nargs="+", help="per-node sqlite db inputs")
    args = ap.parse_args()

    inputs = [d for d in args.dbs if os.path.exists(d)]
    if not inputs:
        sys.stderr.write("no input dbs found\n")
        sys.exit(1)

    out_dir = os.path.dirname(args.out)
    if out_dir and not os.path.isdir(out_dir):
        os.makedirs(out_dir)

    schema = SCHEMA if SCHEMA else schema_from(inputs[0])
    conn = sqlite3.connect(args.out)
    try:
        conn.executescript(schema)
        total_in = 0
        for db in inputs:
            conn.execute("ATTACH ? AS src", (db,))
            cur = conn.execute("SELECT COUNT(*) FROM src.diff_results")
            n = cur.fetchone()[0]
            total_in += n
            conn.execute(
                "INSERT OR REPLACE INTO diff_results "
                "SELECT * FROM src.diff_results")
            conn.commit()          # must commit before DETACH (else 'database src is locked')
            conn.execute("DETACH src")
            sys.stderr.write("  merged %5d rows from %s\n" % (n, db))
        conn.commit()
        final = conn.execute("SELECT COUNT(*) FROM diff_results").fetchone()[0]
    finally:
        conn.close()

    sys.stderr.write("merged %d node dbs: %d input rows -> %d unique rows -> %s\n"
                     % (len(inputs), total_in, final, args.out))


if __name__ == "__main__":
    main()
