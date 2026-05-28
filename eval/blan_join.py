"""eval.blan_join — 3-oracle (z3/cvc5 + BLAN) file-based differential for QF_NIA.

The master's "对拍 from files, run only the misses locally" workflow: join a
finished Xolver run against the cached BLAN CSV (and reuse run_benchmark's z3/cvc5
MISMATCH), then print:
  - DECIDED DISAGREEMENTS  (both decided + differ = soundness bug; exit code 2)
  - BLAN-DECIDED / XOLVER-UNKNOWN  (debug-locally / recovery targets)

Usage:
  python3 -m eval.blan_join --run-dir results/run_... --blan 'blan_QF_NIA_node*.csv'
  python3 -m eval.blan_join --stats <statistics.json> --blan /path/to/blan_dir --json

Python 3.7+ / stdlib only.
"""
import argparse
import json
import sys
from typing import Dict, List, Optional

from eval.loader import load_run_dir, load_statistics_json
from eval.model import CaseResult
from eval.oracle import (BlanRow, blan_debug_targets, decided_disagreements,
                         load_blan_csv, overlap_stats, overlap_warning)

DECIDED = ("sat", "unsat")


def _load_cases(args) -> List[CaseResult]:
    if args.stats:
        return load_statistics_json(args.stats)
    return load_run_dir(args.run_dir)


def write_file_list(blan_map: Dict[str, BlanRow], path: str,
                    decided_only: bool = False) -> int:
    """Write BLAN's keys as a run_benchmark.py --file-list (one key per line).

    Keys are already "<LOGIC>/<family>/<file>.smt2" — run_benchmark resolves
    relative lines against --benchmark-dir, so feeding this list to BOTH BLAN
    and Xolver aligns the two file sets (resolves the selection mismatch).
    """
    keys = sorted(blan_map)
    if decided_only:
        keys = [k for k in keys if blan_map[k].verdict in DECIDED]
    with open(path, "w") as f:
        for k in keys:
            f.write(k + "\n")
    return len(keys)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="3-oracle BLAN-join differential (QF_NIA): decided-disagreements + debug targets.")
    src = p.add_mutually_exclusive_group(required=False)
    src.add_argument("--run-dir", help="A run dir (RUN_DIR/<LOGIC>/statistics.json)")
    src.add_argument("--stats", help="A single statistics.json")
    p.add_argument("--blan", required=True,
                   help="BLAN CSV file, glob (blan_QF_NIA_node*.csv), or dir containing blan_*.csv")
    p.add_argument("--oracle-label", default="z3",
                   help="label for run_benchmark's live MISMATCH oracle (z3/cvc5)")
    p.add_argument("--json", action="store_true", help="emit JSON instead of text")
    p.add_argument("--limit", type=int, default=0, help="print at most N rows per section (0 = all)")
    p.add_argument("--emit-file-list", default=None,
                   help="write BLAN's keys as a run_benchmark --file-list and exit "
                        "(feed both BLAN and Xolver from it to align the file sets)")
    p.add_argument("--decided-only", action="store_true",
                   help="with --emit-file-list: only sat/unsat BLAN keys")
    p.add_argument("--min-overlap", type=float, default=0.10,
                   help="warn loudly if joined/Xolver falls below this (default 0.10)")
    args = p.parse_args(argv)

    blan = load_blan_csv(args.blan)

    # Alignment helper: emit the shared file list and exit (no run dir needed).
    if args.emit_file_list:
        n = write_file_list(blan, args.emit_file_list, decided_only=args.decided_only)
        print("wrote %d BLAN key(s)%s -> %s" %
              (n, " (decided only)" if args.decided_only else "", args.emit_file_list))
        return 0

    if not (args.run_dir or args.stats):
        p.error("one of --run-dir/--stats is required (or use --emit-file-list)")

    cases = _load_cases(args)
    stats = overlap_stats(cases, blan)
    dis = decided_disagreements(cases, blan_map=blan, oracle_label=args.oracle_label)
    targets = blan_debug_targets(cases, blan)

    warn = overlap_warning(stats, threshold=args.min_overlap)

    if args.json:
        print(json.dumps({
            "blan_rows": len(blan),
            "joined_cases": len(cases),
            "overlap": stats,
            "overlap_warning": warn,
            "decided_disagreements": [d.__dict__ for d in dis],
            "debug_targets": [t.__dict__ for t in targets],
        }, indent=2))
        return 2 if dis else 0

    def _emit(rows):
        shown = rows if args.limit <= 0 else rows[:args.limit]
        for r in shown:
            print("  %-52s xolver=%-8s %s=%s" % (r.key, r.xolver_result, r.oracle, r.oracle_result))
        if args.limit and len(rows) > args.limit:
            print("  ... (%d more)" % (len(rows) - args.limit))

    if warn:
        print("=" * 72)
        print("WARNING: " + warn)
        print("=" * 72)
    print("BLAN rows: %d   Xolver QF_NIA cases: %d   joined: %d (%.1f%%)"
          % (stats["blan"], stats["xolver"], stats["joined"], 100.0 * stats["ratio"]))
    print("\n[DECIDED DISAGREEMENTS]  both decided + differ = SOUNDNESS BUG: %d" % len(dis))
    _emit(dis)
    print("\n[BLAN-DECIDED / XOLVER-UNKNOWN]  debug-locally / recovery targets: %d" % len(targets))
    _emit(targets)
    return 2 if dis else 0


if __name__ == "__main__":
    sys.exit(main())
