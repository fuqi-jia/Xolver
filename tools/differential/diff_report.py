#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""diff_report.py -- Stage 1 sanity-check report from a merged full.sqlite.

    python3 diff_report.py --db results/2026-06-XX/full.sqlite \\
            [--out results/2026-06-XX/REPORT.md] [--expected expected_counts.csv]

Emits per-division: case count / xolver-decided rate / oracle-decided rate /
oracle-blind count / disagreement count / regression / recovery, plus the global
0-disagreement (== "0 解错") sanity gate. If any disagreement rows exist they are
listed in full -- each is a soundness candidate that must be triaged before the
data is handed to Stage 2.

--expected takes an optional CSV (division,expected_count) so the report can flag
divisions whose case count doesn't line up with the benchmark inventory (catches
node-slicing bugs where a slice silently dropped files).

Python 3.7+, stdlib only.
"""

import argparse
import csv
import sqlite3
import sys


def pct(num, den):
    if not den:
        return "0.0%"
    return "%.1f%%" % (100.0 * num / den)


def load_expected(path):
    exp = {}
    with open(path, "r", newline="", encoding="utf-8") as fh:
        for row in csv.reader(fh):
            if len(row) >= 2 and row[0].strip() and not row[0].startswith("#"):
                try:
                    exp[row[0].strip()] = int(row[1])
                except ValueError:
                    pass
    return exp


def main():
    ap = argparse.ArgumentParser(description="Stage 1 sanity report from full.sqlite.")
    ap.add_argument("--db", required=True)
    ap.add_argument("--out", default=None, help="REPORT.md path (default: stdout)")
    ap.add_argument("--expected", default=None,
                    help="optional CSV: division,expected_count")
    args = ap.parse_args()

    expected = load_expected(args.expected) if args.expected else {}

    conn = sqlite3.connect(args.db)
    conn.row_factory = sqlite3.Row

    divs = [r[0] for r in conn.execute(
        "SELECT DISTINCT division FROM diff_results ORDER BY division")]

    lines = []
    out = lines.append
    out("# Stage 1 differential — sanity report\n")

    total = conn.execute("SELECT COUNT(*) FROM diff_results").fetchone()[0]
    g_dis = conn.execute(
        "SELECT COUNT(*) FROM diff_results WHERE is_disagreement=1").fetchone()[0]
    g_blind = conn.execute(
        "SELECT COUNT(*) FROM diff_results WHERE is_oracle_blind=1").fetchone()[0]

    gate = "PASS ✅" if g_dis == 0 else ("FAIL ❌ (%d soundness candidates)" % g_dis)
    out("**Total cases:** %d  ·  **divisions:** %d" % (total, len(divs)))
    out("**0-disagreement (0 解错) gate:** %s" % gate)
    out("**oracle-blind (xolver decided, oracle didn't):** %d\n" % g_blind)

    out("## Per-division\n")
    out("| division | cases | exp | xolver-dec | oracle-dec | oracle-blind | disagree | regress | recover |")
    out("|---|--:|--:|--:|--:|--:|--:|--:|--:|")
    for d in divs:
        r = conn.execute(
            "SELECT COUNT(*) c, "
            "SUM(is_decided_by_xolver) xd, "
            "SUM(is_decided_by_oracle) od, "
            "SUM(is_oracle_blind) ob, "
            "SUM(is_disagreement) dis, "
            "SUM(is_regression) reg, "
            "SUM(is_recovery) rec "
            "FROM diff_results WHERE division=?", (d,)).fetchone()
        c = r["c"]
        xd, od, ob = r["xd"] or 0, r["od"] or 0, r["ob"] or 0
        dis, reg, rec = r["dis"] or 0, r["reg"] or 0, r["rec"] or 0
        exp = expected.get(d)
        exp_cell = str(exp) if exp is not None else "-"
        if exp is not None and exp != c:
            exp_cell = "%d ⚠" % exp
        out("| %s | %d | %s | %d (%s) | %d (%s) | %d | %d | %d | %d |" % (
            d, c, exp_cell,
            xd, pct(xd, c), od, pct(od, c), ob, dis, reg, rec))

    if g_dis:
        out("\n## ⚠ Disagreements (soundness candidates — triage before Stage 2)\n")
        out("| key | default | allon | oracle | oracle_solver |")
        out("|---|---|---|---|---|")
        for r in conn.execute(
                "SELECT key, xolver_default_verdict d, xolver_allon_verdict a, "
                "oracle_verdict o, oracle_solver s "
                "FROM diff_results WHERE is_disagreement=1 ORDER BY division, key"):
            out("| `%s` | %s | %s | %s | %s |" % (
                r["key"], r["d"], r["a"], r["o"], r["s"]))

    conn.close()
    text = "\n".join(lines) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
        sys.stderr.write("report -> %s\n" % args.out)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
