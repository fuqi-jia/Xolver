"""eval.diffscore — family-split scoring + 解错 gate + stale/cluster detector.

Over results/diff_*.csv rows:
  - family_split / division_rollup: baseline vs candidate solved@1200, recovered,
    regressed, 解错 (the gate: any 解错 blocks default-ON).
  - jiecuo_clusters / stale_suspects: group 解错 by (division, family, flip) so a
    single-root / stale-binary artifact (1210 edge_closing all sat->unsat) is
    visually one big uniform cluster, not 1210 independent soundness bugs.

Python 3.6+ / stdlib only.
"""
from collections import Counter
from typing import Dict, List

from eval._compat import dataclass
from eval.diffmodel import (DiffRow, correct_solved, is_jiecuo, jiecuo_flip,
                            name_category)


@dataclass
class FamilyScore:
    division: str
    family: str
    total: int = 0
    baseline_solved: int = 0
    candidate_solved: int = 0
    recovered: int = 0
    regressed: int = 0
    jiecuo: int = 0

    @property
    def net_delta(self) -> int:
        return self.candidate_solved - self.baseline_solved


@dataclass
class DivisionScore:
    division: str
    total: int = 0
    baseline_solved: int = 0
    candidate_solved: int = 0
    recovered: int = 0
    regressed: int = 0
    jiecuo: int = 0

    @property
    def net_delta(self) -> int:
        return self.candidate_solved - self.baseline_solved

    @property
    def gate_clear(self) -> bool:
        """0 解错 = the soundness gate (paramount). Necessary, not sufficient."""
        return self.jiecuo == 0

    @property
    def promotable(self) -> bool:
        """Worth promoting to default: soundness gate + positive net solved-delta.
        net <= 0 with 0 解错 still means the bundle is sound but adds no value;
        not a regression in the soundness sense but not a promotion candidate either."""
        return self.gate_clear and self.net_delta > 0


def _tally(rows, obj):
    for r in rows:
        bs = correct_solved(r.baseline, r.oracle)
        cs = correct_solved(r.candidate, r.oracle)
        if bs:
            obj.baseline_solved += 1
        if cs:
            obj.candidate_solved += 1
        if cs and not bs:
            obj.recovered += 1
        if bs and not cs:
            obj.regressed += 1
        if is_jiecuo(r):
            obj.jiecuo += 1
    return obj


def family_split(rows: List[DiffRow]) -> List[FamilyScore]:
    groups: Dict[tuple, List[DiffRow]] = {}
    for r in rows:
        groups.setdefault((r.logic, r.family), []).append(r)
    out = []
    for (lg, fam), rs in sorted(groups.items()):
        out.append(_tally(rs, FamilyScore(division=lg, family=fam, total=len(rs))))
    return out


def division_rollup(rows: List[DiffRow]) -> List[DivisionScore]:
    groups: Dict[str, List[DiffRow]] = {}
    for r in rows:
        groups.setdefault(r.logic, []).append(r)
    return [_tally(rs, DivisionScore(division=lg, total=len(rs)))
            for lg, rs in sorted(groups.items())]


# --------------------------------------------------------------------------- #
# Stale / single-root cluster detector
# --------------------------------------------------------------------------- #
@dataclass
class JiecuoCluster:
    division: str
    family: str
    flip: str
    count: int
    dominant_pattern: str


def jiecuo_clusters(rows: List[DiffRow]) -> List[JiecuoCluster]:
    """解错 grouped by (division, family, flip-direction), with the dominant
    benchmark-name pattern in each. Sorted by count desc."""
    groups: Dict[tuple, List[str]] = {}
    for r in rows:
        if not is_jiecuo(r):
            continue
        groups.setdefault((r.logic, r.family, jiecuo_flip(r)), []).append(name_category(r.key))
    clusters = []
    for (lg, fam, flip), cats in groups.items():
        dom = Counter(cats).most_common(1)[0][0] if cats else "?"
        clusters.append(JiecuoCluster(lg, fam, flip, len(cats), dom))
    clusters.sort(key=lambda c: (-c.count, c.division, c.family, c.flip))
    return clusters


def stale_suspects(clusters: List[JiecuoCluster], min_count: int = 50,
                   dominance: float = 0.7) -> List[JiecuoCluster]:
    """Clusters likely to be a stale-binary / single-root artifact rather than N
    independent bugs: a single (family, flip) bucket that is large in absolute
    terms OR holds the dominant share of all 解错."""
    total = sum(c.count for c in clusters) or 1
    out = []
    for c in clusters:
        if c.count >= min_count or (c.count > 1 and c.count / total >= dominance):
            out.append(c)
    return out


# --------------------------------------------------------------------------- #
# Formatting
# --------------------------------------------------------------------------- #
def format_divisions(divs: List[DivisionScore]) -> str:
    hdr = "{:<14} {:>6} {:>9} {:>9} {:>6} {:>6} {:>9} {:>7} {:>5} {:>6}".format(
        "division", "total", "base@1200", "cand@1200", "net", "recov", "regress",
        "解错", "GATE", "PROMO")
    lines = [hdr, "-" * len(hdr)]
    for d in divs:
        lines.append("{:<14} {:>6} {:>9} {:>9} {:>+6d} {:>6} {:>9} {:>7} {:>5} {:>6}".format(
            d.division, d.total, d.baseline_solved, d.candidate_solved, d.net_delta,
            d.recovered, d.regressed, d.jiecuo,
            "yes" if d.gate_clear else "NO",
            "yes" if d.promotable else "no"))
    return "\n".join(lines)


def format_stale(clusters: List[JiecuoCluster], suspects: List[JiecuoCluster]) -> str:
    susp = {(c.division, c.family, c.flip) for c in suspects}
    lines = ["解错 by family + flip-direction (★=likely stale/single-root, not N bugs):",
             "{:<3} {:<14} {:<26} {:<14} {:>6} {:<}".format(
                 "", "division", "family", "flip", "count", "dominant-pattern")]
    for c in clusters:
        mark = "★" if (c.division, c.family, c.flip) in susp else " "
        lines.append("{:<3} {:<14} {:<26} {:<14} {:>6} {:<}".format(
            mark, c.division, c.family[:26], c.flip, c.count, c.dominant_pattern))
    return "\n".join(lines)
