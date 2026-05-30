#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""diff_ingest.py -- ingest rich differential CSV(s) into a per-run SQLite db.

One row per benchmark case. Raw columns come straight from the CSV emitted by
tools/diff_common.sh::run_one_rich; the derived flags (is_decided_*, is_oracle_blind,
is_disagreement, is_regression, is_recovery) are computed here so the shell side
stays dependency-free.

Usage:
    python3 diff_ingest.py --sqlite panda9_<ts>.sqlite [--csv-mirror panda9_<ts>.csv] \\
            diff_QF_UF_node9.csv diff_QF_LRA_node9.csv ...

Python 3.7+, stdlib only (argparse, csv, sqlite3). No third-party deps so it runs
on a bare panda node. If python3 is absent the caller skips this step entirely and
the rich CSV remains the source of truth.
"""

import argparse
import csv
import os
import sqlite3
import sys

DECIDED = ("sat", "unsat")

# Raw columns, in CSV order (must match diff_common.sh RICH_HEADER).
RAW_COLS = [
    "key", "division", "file_path", "file_size_bytes", "declared_logic",
    "xolver_default_verdict", "xolver_default_time_ms",
    "xolver_allon_verdict", "xolver_allon_time_ms",
    "oracle_solver", "oracle_verdict", "oracle_time_ms",
    "panda_node", "run_timestamp", "xolver_git_tip",
    "file_dir_prefix", "file_name_stem",
]

DERIVED_COLS = [
    "is_decided_by_xolver", "is_decided_by_oracle", "is_oracle_blind",
    "is_disagreement", "is_regression", "is_recovery",
]

SCHEMA = """
CREATE TABLE IF NOT EXISTS diff_results (
    key TEXT PRIMARY KEY,
    division TEXT NOT NULL,
    file_path TEXT NOT NULL,
    file_size_bytes INTEGER,
    declared_logic TEXT,

    xolver_default_verdict TEXT,
    xolver_default_time_ms INTEGER,
    xolver_allon_verdict TEXT,
    xolver_allon_time_ms INTEGER,

    oracle_solver TEXT NOT NULL,
    oracle_verdict TEXT,
    oracle_time_ms INTEGER,

    is_decided_by_xolver INTEGER,
    is_decided_by_oracle INTEGER,
    is_oracle_blind INTEGER,
    is_disagreement INTEGER,
    is_regression INTEGER,
    is_recovery INTEGER,

    panda_node INTEGER,
    run_timestamp TEXT,
    xolver_git_tip TEXT,
    file_dir_prefix TEXT,
    file_name_stem TEXT
);
CREATE INDEX IF NOT EXISTS idx_division     ON diff_results(division);
CREATE INDEX IF NOT EXISTS idx_oracle_blind ON diff_results(is_oracle_blind);
CREATE INDEX IF NOT EXISTS idx_disagreement ON diff_results(is_disagreement);
CREATE INDEX IF NOT EXISTS idx_dir_prefix   ON diff_results(file_dir_prefix);
"""

ALL_COLS = (
    RAW_COLS[:12] + DERIVED_COLS + RAW_COLS[12:]
)  # insertion order = table column order


def _int(v, default=0):
    try:
        return int(str(v).strip())
    except (ValueError, TypeError):
        return default


def derive(row):
    """Compute the six derived flags from raw verdicts."""
    dv = (row.get("xolver_default_verdict") or "").strip().lower()
    av = (row.get("xolver_allon_verdict") or "").strip().lower()
    ov = (row.get("oracle_verdict") or "").strip().lower()

    default_dec = dv in DECIDED
    allon_dec = av in DECIDED
    oracle_dec = ov in DECIDED
    xolver_dec = default_dec or allon_dec

    # Disagreement = a soundness candidate: oracle decided AND some xolver config
    # decided the OPPOSITE. Checked for both configs so an unsoundness that only
    # appears under --allon (flag-pair unsoundness) is still caught.
    disagreement = oracle_dec and (
        (default_dec and dv != ov) or (allon_dec and av != ov)
    )

    return {
        "is_decided_by_xolver": 1 if xolver_dec else 0,
        "is_decided_by_oracle": 1 if oracle_dec else 0,
        "is_oracle_blind": 1 if (xolver_dec and not oracle_dec) else 0,
        "is_disagreement": 1 if disagreement else 0,
        "is_regression": 1 if (default_dec and not allon_dec) else 0,
        "is_recovery": 1 if (allon_dec and not default_dec) else 0,
    }


def load_csv(path):
    rows = []
    with open(path, "r", newline="", encoding="utf-8", errors="replace") as fh:
        reader = csv.DictReader(fh)
        for raw in reader:
            if not raw.get("key"):
                continue
            row = dict(raw)
            row["file_size_bytes"] = _int(row.get("file_size_bytes"))
            row["xolver_default_time_ms"] = _int(row.get("xolver_default_time_ms"))
            row["xolver_allon_time_ms"] = _int(row.get("xolver_allon_time_ms"))
            row["oracle_time_ms"] = _int(row.get("oracle_time_ms"))
            row["panda_node"] = _int(row.get("panda_node"), default=-1)
            row.update(derive(row))
            rows.append(row)
    return rows


def main():
    ap = argparse.ArgumentParser(description="Ingest rich differential CSV(s) into SQLite.")
    ap.add_argument("--sqlite", required=True, help="output sqlite db path")
    ap.add_argument("--csv-mirror", default=None,
                    help="optional combined CSV dump (raw + derived flags)")
    ap.add_argument("csvs", nargs="+", help="rich CSV input(s)")
    args = ap.parse_args()

    all_rows = []
    for path in args.csvs:
        if not os.path.exists(path):
            sys.stderr.write("  [ingest] skip missing %s\n" % path)
            continue
        all_rows.extend(load_csv(path))

    conn = sqlite3.connect(args.sqlite)
    try:
        conn.executescript(SCHEMA)
        placeholders = ",".join(["?"] * len(ALL_COLS))
        sql = "INSERT OR REPLACE INTO diff_results (%s) VALUES (%s)" % (
            ",".join(ALL_COLS), placeholders)
        conn.executemany(sql, [tuple(r.get(c) for c in ALL_COLS) for r in all_rows])
        conn.commit()
        n = conn.execute("SELECT COUNT(*) FROM diff_results").fetchone()[0]
    finally:
        conn.close()

    sys.stderr.write("  [ingest] %d rows -> %s (%d total in db)\n"
                     % (len(all_rows), args.sqlite, n))

    if args.csv_mirror:
        with open(args.csv_mirror, "w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(ALL_COLS)
            for r in all_rows:
                w.writerow([r.get(c) for c in ALL_COLS])
        sys.stderr.write("  [ingest] csv mirror -> %s\n" % args.csv_mirror)


if __name__ == "__main__":
    main()
