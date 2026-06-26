#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""diff_query.py -- named SQL queries over a differential full.sqlite.

Schema-driven user interface to the diff_results table (see eval/oracle_schema.md).
Master uses this for the Stage-2 catalog (per-division SQL results, copy-pasteable
markdown) and for Stage-4 daily delta checks -- no hand-written SQL.

    python3 tools/diff_query.py --db full.sqlite --query strength_catalog --division QF_NIA
    python3 tools/diff_query.py --db full.sqlite --query weakness_clusters --division QF_UF --top 30
    python3 tools/diff_query.py --db full.sqlite --query disagreement_audit
    python3 tools/diff_query.py --db full.sqlite --query per_division_summary
    python3 tools/diff_query.py --db full.sqlite --list-queries
    python3 tools/diff_query.py --db full.sqlite --query oracle_blind --out blind.csv

Output: markdown table on stdout (stable for copy-paste); optional --out writes CSV.
A one-line "N rows" summary goes to stderr so stdout stays pure markdown.

Python 3.7+, stdlib only (argparse, csv, sqlite3).
"""

import argparse
import csv
import sqlite3
import sys

# "decided" = sat|unsat. Each query is pure SQL over diff_results columns + is_* flags.
# divisionable=True -> --division appends `division = ?`. needs_inherit_col -> append the
# audit column when the db has it (older 23-col baselines don't).
QUERIES = {
    "strength_catalog": {
        "desc": "xolver decided, oracle did NOT -- xolver-unique wins (SOTA narrative; always protect)",
        "select": "key, division, xolver_default_verdict AS default_v, "
                  "xolver_allon_verdict AS allon_v, oracle_solver, oracle_verdict, "
                  "xolver_allon_time_ms AS allon_ms, file_dir_prefix",
        "predicates": ["is_oracle_blind=1"],
        "order": "division, file_dir_prefix, key",
        "divisionable": True,
    },
    "weakness_clusters": {
        "desc": "oracle decided, xolver did NOT -- grouped by file_dir_prefix, biggest gaps first",
        "select": "division, file_dir_prefix, COUNT(*) AS n_unsolved, "
                  "SUM(CASE WHEN oracle_verdict='sat'   THEN 1 ELSE 0 END) AS oracle_sat, "
                  "SUM(CASE WHEN oracle_verdict='unsat' THEN 1 ELSE 0 END) AS oracle_unsat",
        "predicates": ["is_decided_by_oracle=1", "is_decided_by_xolver=0"],
        "group": "division, file_dir_prefix",
        "order": "n_unsolved DESC, division, file_dir_prefix",
        "divisionable": True,
    },
    "disagreement_audit": {
        "desc": "xolver verdict conflicts with oracle -- candidate soundness bugs (bidirectional)",
        "select": "key, division, xolver_default_verdict AS default_v, "
                  "xolver_allon_verdict AS allon_v, oracle_solver, oracle_verdict",
        "predicates": ["is_disagreement=1"],
        "order": "division, key",
        "divisionable": True,
        "needs_inherit_col": True,
    },
    "oracle_blind": {
        "desc": "NEITHER xolver nor oracle decided (both unknown/timeout/error) -- cert-audit lane "
                "candidates. NOTE: distinct from the is_oracle_blind flag (= strength_catalog).",
        "select": "key, division, xolver_default_verdict AS default_v, "
                  "xolver_allon_verdict AS allon_v, oracle_solver, oracle_verdict, file_dir_prefix",
        "predicates": ["is_decided_by_xolver=0", "is_decided_by_oracle=0"],
        "order": "division, file_dir_prefix, key",
        "divisionable": True,
    },
    "regression": {
        "desc": "default decided, --allon did NOT -- completeness regression introduced by a flag",
        "select": "key, division, xolver_default_verdict AS default_v, "
                  "xolver_allon_verdict AS allon_v, oracle_verdict, "
                  "xolver_default_time_ms AS default_ms, xolver_allon_time_ms AS allon_ms",
        "predicates": ["is_regression=1"],
        "order": "division, key",
        "divisionable": True,
    },
    "recovery": {
        "desc": "default did NOT decide, --allon did -- net gain from a flag",
        "select": "key, division, xolver_default_verdict AS default_v, "
                  "xolver_allon_verdict AS allon_v, oracle_verdict, xolver_allon_time_ms AS allon_ms",
        "predicates": ["is_recovery=1"],
        "order": "division, key",
        "divisionable": True,
    },
    "per_division_summary": {
        "desc": "per-division roll-up: total / decided / unique-win / disagreement / regress / recover",
        "select": "division, COUNT(*) AS total, "
                  "SUM(is_decided_by_xolver) AS xolver_decided, "
                  "SUM(is_decided_by_oracle) AS oracle_decided, "
                  "SUM(is_oracle_blind) AS unique_win, "
                  "SUM(is_disagreement) AS disagreements, "
                  "SUM(is_regression) AS regressions, "
                  "SUM(is_recovery) AS recoveries",
        "predicates": [],
        "group": "division",
        "order": "division",
        "divisionable": True,
    },
    "xolver_unique_unsat": {
        "desc": "xolver UNSAT while oracle did NOT refute (timeout/unknown/error) -- MUST cert-audit "
                "(unsound-risk: a wrong UNSAT has no model-validation backstop)",
        "select": "key, division, xolver_default_verdict AS default_v, "
                  "xolver_allon_verdict AS allon_v, oracle_solver, oracle_verdict, file_dir_prefix",
        "predicates": ["(xolver_default_verdict='unsat' OR xolver_allon_verdict='unsat')",
                       "is_decided_by_oracle=0"],
        "order": "division, file_dir_prefix, key",
        "divisionable": True,
        "needs_inherit_col": True,
    },
}


def has_col(conn, col):
    return col in {r[1] for r in conn.execute("PRAGMA table_info(diff_results)")}


def build_sql(q, division, top, conn):
    select = q["select"]
    if q.get("needs_inherit_col"):
        select += ", " + ("oracle_inherited_from_run"
                          if has_col(conn, "oracle_inherited_from_run")
                          else "NULL AS oracle_inherited_from_run")
    preds = list(q.get("predicates", []))
    params = []
    if division and q.get("divisionable", True):
        preds.append("division = ?")
        params.append(division)
    where = (" WHERE " + " AND ".join(preds)) if preds else ""
    group = (" GROUP BY " + q["group"]) if q.get("group") else ""
    order = (" ORDER BY " + q["order"]) if q.get("order") else ""
    limit = (" LIMIT %d" % int(top)) if (top is not None and int(top) > 0) else ""
    return "SELECT %s FROM diff_results%s%s%s%s" % (select, where, group, order, limit), params


def run_query(conn, name, division=None, top=None):
    """-> (columns, rows). Raises KeyError on unknown query name."""
    q = QUERIES[name]
    sql, params = build_sql(q, division, top, conn)
    cur = conn.execute(sql, params)
    cols = [d[0] for d in cur.description]
    rows = cur.fetchall()
    return cols, rows


def to_markdown(cols, rows):
    out = ["| " + " | ".join(cols) + " |",
           "|" + "|".join(["---"] * len(cols)) + "|"]
    for r in rows:
        out.append("| " + " | ".join("" if v is None else str(v) for v in r) + " |")
    if not rows:
        out.append("| " + " | ".join(["_(no rows)_"] + [""] * (len(cols) - 1)) + " |")
    return "\n".join(out) + "\n"


def write_csv(path, cols, rows):
    with open(path, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(cols)
        for r in rows:
            w.writerow(["" if v is None else v for v in r])


def main():
    ap = argparse.ArgumentParser(description="Named SQL queries over a differential full.sqlite.")
    ap.add_argument("--db", help="full.sqlite path")
    ap.add_argument("--query", help="named query (see --list-queries)")
    ap.add_argument("--division", default=None, help="restrict to one division, e.g. QF_NIA")
    ap.add_argument("--top", type=int, default=None, help="LIMIT N rows")
    ap.add_argument("--out", default=None, help="also write results as CSV")
    ap.add_argument("--list-queries", action="store_true")
    args = ap.parse_args()

    if args.list_queries:
        width = max(len(k) for k in QUERIES)
        for name in sorted(QUERIES):
            sys.stdout.write("%-*s  %s\n" % (width, name, QUERIES[name]["desc"]))
        return

    if not args.db or not args.query:
        ap.error("--db and --query are required (or use --list-queries)")
    if args.query not in QUERIES:
        ap.error("unknown query '%s'. Available: %s" % (args.query, ", ".join(sorted(QUERIES))))

    conn = sqlite3.connect(args.db)
    try:
        cols, rows = run_query(conn, args.query, args.division, args.top)
    finally:
        conn.close()

    sys.stdout.write(to_markdown(cols, rows))
    if args.out:
        write_csv(args.out, cols, rows)
        sys.stderr.write("  csv -> %s\n" % args.out)
    sys.stderr.write("  [%s%s] %d rows\n"
                     % (args.query, ("/" + args.division) if args.division else "", len(rows)))


if __name__ == "__main__":
    main()
