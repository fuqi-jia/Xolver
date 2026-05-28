"""eval.select — family-split train/val file-list generator for the autotuner.

Produces the "family-split, competition-representative set" the autotuner trains
on: enumerate a logic's benchmark files, split by family (val sees families the
train set never has — reuses eval.families), optionally cap per family so one
huge submitter family can't dominate (mirrors the competition's large-logic cap),
and emit run_benchmark --file-list files (keys = <LOGIC>/<family>/<file>.smt2,
resolved against --benchmark-dir). Feed the train list to `autotune plan
--file-list`; keep the val list for the held-out check.

Python 3.6+ / stdlib only.
"""
import argparse
import os
import random
import sys
from typing import List, Optional, Tuple

from eval.families import split_families
from eval.model import CaseResult, family_of, normalize_key


def enumerate_cases(logic: str, benchmark_dir: str) -> List[CaseResult]:
    """All .smt2 under <benchmark_dir>/<logic> as keyed CaseResult stubs."""
    root = os.path.join(benchmark_dir, logic)
    cases: List[CaseResult] = []
    for dirpath, _dirs, filenames in os.walk(root):
        for fn in filenames:
            if not fn.endswith(".smt2"):
                continue
            p = os.path.join(dirpath, fn)
            key = normalize_key(p, logic) or (logic + "/" + os.path.relpath(p, root))
            cases.append(CaseResult(key=key, logic=logic, family=family_of(key, logic),
                                    path=p, result="", time=0.0))
    cases.sort(key=lambda c: c.key)
    return cases


def cap_per_family(cases: List[CaseResult], cap: int, seed: int) -> List[CaseResult]:
    """Keep at most `cap` files per family (seeded sample; cap<=0 = keep all)."""
    if not cap or cap <= 0:
        return list(cases)
    groups = {}
    for c in cases:
        groups.setdefault(c.family, []).append(c)
    out: List[CaseResult] = []
    for fam in sorted(groups):
        items = sorted(groups[fam], key=lambda c: c.key)
        if len(items) > cap:
            rng = random.Random("%s:%d" % (fam, seed))
            items = sorted(rng.sample(items, cap), key=lambda c: c.key)
        out.extend(items)
    out.sort(key=lambda c: c.key)
    return out


def select_cases(logic: str, benchmark_dir: str, val_fraction: float = 0.3,
                 seed: int = 0, per_family_cap: int = 0
                 ) -> Tuple[List[CaseResult], List[CaseResult]]:
    cases = enumerate_cases(logic, benchmark_dir)
    train, val = split_families(cases, val_fraction, seed)
    return (cap_per_family(train, per_family_cap, seed),
            cap_per_family(val, per_family_cap, seed))


def write_keys(cases: List[CaseResult], path: str) -> int:
    with open(path, "w") as f:
        for c in sorted(cases, key=lambda c: c.key):
            f.write(c.key + "\n")
    return len(cases)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Family-split train/val --file-list generator for the autotuner.")
    p.add_argument("--logic", required=True)
    p.add_argument("--benchmark-dir", required=True)
    p.add_argument("--val-fraction", type=float, default=0.3)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--per-family-cap", type=int, default=0,
                   help="max files per family per side (0 = all)")
    p.add_argument("--out-train", required=True)
    p.add_argument("--out-val", default=None)
    args = p.parse_args(argv)

    train, val = select_cases(args.logic, args.benchmark_dir, args.val_fraction,
                              args.seed, args.per_family_cap)
    n_tr = write_keys(train, args.out_train)
    print("train: %d files / %d families -> %s"
          % (n_tr, len({c.family for c in train}), args.out_train))
    if args.out_val:
        n_va = write_keys(val, args.out_val)
        print("val:   %d files / %d families -> %s"
              % (n_va, len({c.family for c in val}), args.out_val))
    return 0


if __name__ == "__main__":
    sys.exit(main())
