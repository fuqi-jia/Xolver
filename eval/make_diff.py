"""eval.make_diff — join a baseline run + candidate run + cached oracle into diff_*.csv.

The "join the cache, don't re-run z3" piece of the re-run harness: given a fresh
baseline (floors) run dir and candidate (floors+flag) run dir, plus the cached z3
verdicts, emit the authoritative diff_<logic>_node<i>.csv (key,baseline,candidate,
oracle). The oracle column stays z3 (BLAN/cvc5 fold in at report time via
eval.oracle3); never re-runs a solver.

  python3 -m eval.make_diff --baseline-run <dir> --candidate-run <dir> \
      --oracle 'results/z3_QF_NIA_node*.csv' --out results/diff_QF_NIA_node1.csv

Python 3.6+ / stdlib only.
"""
import argparse
import csv
import sys
from typing import List, Optional, Tuple

from eval.loader import load_run_dir
from eval.oracle3 import load_verdict_cache


def make_diff_rows(baseline_dir: str, candidate_dir: str,
                   oracle_cache) -> List[Tuple[str, str, str, str]]:
    base = {c.key: c.result for c in load_run_dir(baseline_dir)}
    cand = {c.key: c.result for c in load_run_dir(candidate_dir)}
    oracle = load_verdict_cache(oracle_cache)
    rows = []
    for k in sorted(cand):
        ov = oracle[k].verdict if k in oracle else "missing"
        rows.append((k, base.get(k, "missing"), cand[k], ov))
    return rows


def write_diff(rows: List[Tuple[str, str, str, str]], out_csv: str) -> int:
    with open(out_csv, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["key", "baseline", "candidate", "oracle"])
        for r in rows:
            w.writerow(r)
    return len(rows)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Join baseline+candidate runs with the cached oracle into diff_*.csv.")
    p.add_argument("--baseline-run", required=True, help="baseline (floors) run dir")
    p.add_argument("--candidate-run", required=True, help="candidate (floors+flag) run dir")
    p.add_argument("--oracle", required=True, help="cached z3 verdicts (z3_*.csv / glob / dir)")
    p.add_argument("--out", required=True, help="output diff_*.csv")
    args = p.parse_args(argv)
    rows = make_diff_rows(args.baseline_run, args.candidate_run, args.oracle)
    n = write_diff(rows, args.out)
    print("wrote %d rows -> %s" % (n, args.out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
