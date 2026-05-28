#!/usr/bin/env python3
"""Parse run_benchmark statistics.json -> recoverable / recoverable-slow / unsound buckets.

recoverable      : xolver unknown/error/killed, oracle definite (sat|unsat)
recoverable-slow : xolver timeout, oracle definite
UNSOUND          : xolver sat vs oracle unsat (or vice versa)  <-- ALARM
Usage: python3 NOTES/inv_parse.py NOTES/run_QF_UFNRA/QF_UFNRA/statistics.json
"""
import json, sys

NO_ANSWER = {"unknown", "error", "killed"}
DEFINITE = {"sat", "unsat"}


def main(path):
    with open(path) as f:
        data = json.load(f)
    rows = data["results"]
    rec, slow, unsound, other = [], [], [], []
    for r in rows:
        x, c = r["xolver_result"], r["compare_result"]
        f_ = r["file"]
        if x in DEFINITE and c in DEFINITE and x != c:
            unsound.append((f_, x, c))
        elif x in NO_ANSWER and c in DEFINITE:
            rec.append((f_, x, c, round(r.get("xolver_time", 0), 1)))
        elif x == "timeout" and c in DEFINITE:
            slow.append((f_, x, c, round(r.get("xolver_time", 0), 1)))
        elif x in DEFINITE and x == c:
            pass  # correct
        else:
            other.append((f_, x, c))
    n = len(rows)
    correct = sum(1 for r in rows if r["xolver_result"] in DEFINITE
                  and r["xolver_result"] == r["compare_result"])
    print(f"=== {path} : {n} cases ===")
    print(f"correct={correct}  recoverable={len(rec)}  recoverable-slow={len(slow)}"
          f"  UNSOUND={len(unsound)}  other={len(other)}")
    if unsound:
        print("\n!!! UNSOUND (xolver vs oracle disagree on definite) !!!")
        for f_, x, c in unsound:
            print(f"  {f_}  xolver={x} oracle={c}")
    if rec:
        print("\n-- recoverable (xolver no-answer, oracle definite) --")
        for f_, x, c, t in rec:
            print(f"  [{c}] {f_}  (xolver={x} {t}s)")
    if slow:
        print("\n-- recoverable-slow (xolver timeout, oracle definite) --")
        for f_, x, c, t in slow:
            print(f"  [{c}] {f_}  ({t}s)")


if __name__ == "__main__":
    for p in sys.argv[1:]:
        main(p)
