"""eval.promote — per-division × flag-config promotion report.

The table master needs to decide what collapses into default: for each candidate
flag-config, per division, the net solved-delta@1200 and 解错, and whether the
config is promotable (0-解错 across ALL its divisions). 8-division 0-解错 = green light.

  python3 -m eval.promote \
      --config modular='results/diff_QF_NIA_modular_node*.csv' \
      --config subtropical='results/diff_QF_NRA_subtropical_node*.csv' \
      --blan 'results/blan_QF_NIA_node*.csv'

Joins cached oracles only (no z3 re-run). exit 2 if any config is blocked.
Python 3.6+ / stdlib only.
"""
import argparse
import sys
from typing import List, Optional

from eval._compat import dataclass
from eval.diffmodel import load_diff
from eval.diffscore import DivisionScore, division_rollup
from eval.oracle3 import build_oracle3, load_verdict_cache, rescore_with_oracle3


@dataclass
class ConfigReport:
    name: str
    divisions: List[DivisionScore]


def score_config(name: str, diff_paths, z3=None, cvc5=None, blan=None) -> ConfigReport:
    rows = load_diff(diff_paths)
    if z3 or cvc5 or blan:
        o3 = build_oracle3(
            z3_map=load_verdict_cache(z3) if z3 else None,
            cvc5_map=load_verdict_cache(cvc5) if cvc5 else None,
            blan_map=load_verdict_cache(blan) if blan else None)
        rows = rescore_with_oracle3(rows, o3)
    return ConfigReport(name=name, divisions=division_rollup(rows))


def config_promotable(cr: ConfigReport) -> bool:
    return bool(cr.divisions) and all(d.promotable for d in cr.divisions)


def config_net(cr: ConfigReport) -> int:
    return sum(d.net_delta for d in cr.divisions)


def config_jiecuo(cr: ConfigReport) -> int:
    return sum(d.jiecuo for d in cr.divisions)


def promotion_table(configs: List[ConfigReport]) -> str:
    hdr = "{:<16} {:<12} {:>9} {:>7} {:>6}".format("config", "division", "net@1200", "解错", "PROMO")
    lines = [hdr, "-" * len(hdr)]
    for cr in configs:
        for d in cr.divisions:
            lines.append("{:<16} {:<12} {:>+9d} {:>7} {:>6}".format(
                cr.name[:16], d.division, d.net_delta, d.jiecuo,
                "yes" if d.promotable else "NO"))
        verdict = ("PROMOTABLE (0-解错, +%d solved)" % config_net(cr) if config_promotable(cr)
                   else "BLOCKED (%d 解错 — triage stale vs real)" % config_jiecuo(cr))
        lines.append("  => %-14s %s" % (cr.name, verdict))
        lines.append("-" * len(hdr))
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Per-division × flag-config promotion report.")
    p.add_argument("--config", action="append", default=[], metavar="NAME=GLOB",
                   help="repeatable: a flag-config name and its diff_*.csv glob")
    p.add_argument("--z3", default=None, help="z3 verdict cache (3-oracle join)")
    p.add_argument("--cvc5", default=None, help="cvc5 verdict cache (3-oracle join)")
    p.add_argument("--blan", default=None, help="BLAN verdict cache (3-oracle join)")
    args = p.parse_args(argv)
    if not args.config:
        p.error("at least one --config NAME=GLOB is required")

    configs = []
    for spec in args.config:
        name, sep, glob = spec.partition("=")
        if not sep:
            p.error("--config must be NAME=GLOB, got %r" % spec)
        configs.append(score_config(name, glob, args.z3, args.cvc5, args.blan))

    print(promotion_table(configs))
    promotable = [c.name for c in configs if config_promotable(c)]
    print("\npromotable now (0-解错): %s" % (", ".join(promotable) if promotable else "(none)"))
    return 0 if len(promotable) == len(configs) else 2


if __name__ == "__main__":
    sys.exit(main())
