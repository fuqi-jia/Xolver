"""eval.diffreport — score results/diff_*.csv: per-division solved-delta, 解错
gate, and the stale/single-root cluster view.

  python3 -m eval.diffreport --diff 'results/diff_*.csv'
  python3 -m eval.diffreport --diff results/ --by family --min-cluster 100

File-based (joins the landed diff; never re-runs z3). exit 2 if any 解错.
Python 3.6+ / stdlib only.
"""
import argparse
import sys
from typing import List, Optional

from eval.diffmodel import load_diff
from eval.diffscore import (division_rollup, family_split, format_divisions,
                            format_stale, jiecuo_clusters, stale_suspects)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Score diff_*.csv: solved-delta + 解错 gate + stale clusters.")
    p.add_argument("--diff", default="results/diff_*.csv",
                   help="diff_*.csv file, glob, or dir (default: results/diff_*.csv)")
    p.add_argument("--by", default=None, choices=["family"],
                   help="also dump the per-family table")
    p.add_argument("--min-cluster", type=int, default=100,
                   help="abs 解错-cluster size to flag as likely stale/single-root")
    args = p.parse_args(argv)

    rows = load_diff(args.diff)
    if not rows:
        print("no diff rows loaded from %r" % args.diff)
        return 1
    divs = division_rollup(rows)
    clusters = jiecuo_clusters(rows)
    suspects = stale_suspects(clusters, min_count=args.min_cluster)

    total_jiecuo = sum(d.jiecuo for d in divs)
    stale_jiecuo = sum(c.count for c in suspects)

    print("== per-division solved-delta + 解错 gate (%d cases) ==" % len(rows))
    print(format_divisions(divs))
    promotable = [d.division for d in divs if d.promotable]
    print("\npromotable (0-解错): %s" % (", ".join(promotable) if promotable else "(none)"))

    if total_jiecuo:
        print("\n== 解错 triage ==")
        print("total 解错 = %d  |  in likely-stale/single-root clusters = %d  |  residual (scattered) = %d"
              % (total_jiecuo, stale_jiecuo, total_jiecuo - stale_jiecuo))
        print(format_stale(clusters, suspects))
        print("\nNOTE: ★ clusters are one family flipping one direction at scale = likely a "
              "stale-binary / single-root artifact (re-run with the fresh binary, harness #4), "
              "NOT N independent bugs. Residual scattered 解错 are the real soundness targets.")

    if args.by == "family":
        print("\n== per-family (families with movement) ==")
        hdr = "{:<14} {:<26} {:>5} {:>6} {:>7} {:>5}".format(
            "division", "family", "net", "recov", "regress", "解错")
        print(hdr); print("-" * len(hdr))
        for f in family_split(rows):
            if f.net_delta or f.regressed or f.jiecuo:
                print("{:<14} {:<26} {:>+5d} {:>6} {:>7} {:>5}".format(
                    f.division, f.family[:26], f.net_delta, f.recovered, f.regressed, f.jiecuo))

    print("\nGATE: %s" % ("0 解错 across all divisions — clean" if total_jiecuo == 0
                          else "%d 解错 present — NOT default-ON until triaged (see clusters)" % total_jiecuo))
    return 2 if total_jiecuo else 0


if __name__ == "__main__":
    sys.exit(main())
