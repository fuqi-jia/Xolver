#!/usr/bin/env python3
"""extract_oracle_cache.py — extract oracle cache TSV from a prior full.sqlite.

Output: TSV with columns: key, oracle_solver, oracle_verdict, oracle_time_ms
Tab-separated (avoid CSV-quote issues with paths containing commas).

Usage:
    python3 tools/extract_oracle_cache.py \\
        --baseline results/2026-05-31/full_30s.sqlite \\
        --out tools/oracle_cache.tsv
"""
import argparse
import sqlite3
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", required=True, help="full.sqlite from prior batch")
    ap.add_argument("--out", required=True, help="output TSV path")
    ap.add_argument("--include-error", action="store_true",
                    help="include cases where oracle had error/timeout (default: skip)")
    args = ap.parse_args()

    db = sqlite3.connect(args.baseline)

    where_clauses = ["oracle_verdict IS NOT NULL", "key IS NOT NULL"]
    if not args.include_error:
        where_clauses.append("oracle_verdict IN ('sat', 'unsat', 'timeout', 'unknown')")
    where = " AND ".join(where_clauses)

    sql = f"""
        SELECT key, oracle_solver, oracle_verdict, oracle_time_ms
        FROM diff_results
        WHERE {where}
        ORDER BY key
    """
    rows = db.execute(sql).fetchall()

    with open(args.out, "w") as f:
        f.write("key\toracle_solver\toracle_verdict\toracle_time_ms\n")
        for r in rows:
            key = (r[0] or "").replace("\t", " ").replace("\n", " ")  # safety
            solver = r[1] or ""
            verdict = r[2] or ""
            time_ms = r[3] or 0
            f.write(f"{key}\t{solver}\t{verdict}\t{time_ms}\n")

    by_verdict = {}
    for r in rows:
        by_verdict[r[2] or "?"] = by_verdict.get(r[2] or "?", 0) + 1
    print(f"extracted {len(rows)} oracle cache entries → {args.out}")
    print(f"  by verdict: {by_verdict}")


if __name__ == "__main__":
    main()
