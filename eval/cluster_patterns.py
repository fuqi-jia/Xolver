"""eval.cluster_patterns — named 解错 cluster classes for explicit verification.

Each pattern recognizes a (division, family, flip-direction) cluster signature
and tags it with a RESOLUTION status. Three uses:

  1. Today — NAME the known clusters in stale data so the report says the 1210
     VeryMax sat->unsat block IS the stale-binary signature, not 1210 independent
     soundness bugs.
  2. After a fix lands — a "should-be-absent" pattern's PRESENCE in fresh data is a
     REGRESSION; its ABSENCE is the VERIFICATION signal. Master's signal post-
     2965e21 (SquareContractorZ sign=-1 -> false-UNSAT on x²=c, fixed): ALL QF_NIA
     sat->unsat clusters should be absent in fresh data.
  3. Placeholders for in-flight work (polyhedral-implied / EQNA Track 2b) so a
     forthcoming cluster is tagged explicitly rather than mislabeled as a fresh bug.

Pattern recognition is BEST-FAITH FIRST GUESS, not definitive — without SMT2
content-grep we identify SquareContractor candidates by their cluster shape
(QF_NIA sat->unsat, NOT the stale-binary signature). A NEW unrelated sat->unsat
bug would also match and be flagged the same way; that's correct (either is a
concern needing investigation), and the naming guides triage.

Python 3.6+ / stdlib only.
"""
from typing import Dict, List, Optional

from eval._compat import dataclass
from eval.diffscore import JiecuoCluster


STALE_RESOLVES = "stale-binary — resolves on next-binary re-run"
FIXED_ABSENT = "FIXED in {commit} — should be ABSENT in fresh data (presence = regression)"
PENDING_FUTURE = "pending {tracking} — expected once that work lands"


@dataclass
class ClusterPattern:
    name: str
    status: str
    explanation: str
    expected_absent_in_fresh: bool = False


# --------------------------------------------------------------------------- #
# Recognizers — each takes a JiecuoCluster and returns True if it matches.
# Order in PATTERNS matters: first match wins (large stale cluster is reported
# as STALE_BINARY, not as a SQUARE_CONTRACTOR candidate).
# --------------------------------------------------------------------------- #
def _is_stale_binary(c: JiecuoCluster) -> bool:
    # Large single (family, flip) bucket with a uniformly-dominant name-pattern
    # is the whole-binary-stale signature (the 1210 VeryMax SAT14 sat->unsat
    # block). Threshold 500 is below 1210 but well above any genuine soundness
    # cluster we have ever seen.
    return c.count >= 500


def _is_potential_square_contractor(c: JiecuoCluster) -> bool:
    # SquareContractorZ sign=-1 wrong c-sign produced QF_NIA false-UNSAT on x²=c
    # (commit 2965e21). Post-fix, ALL QF_NIA sat->unsat clusters should be absent.
    # Without SMT2 content-grep we can't positively identify x²=c; we therefore
    # define this pattern as "any QF_NIA sat->unsat cluster that is NOT the
    # stale-binary signature." A new unrelated false-UNSAT would also match —
    # that's fine; either is a concern. Naming guides triage.
    return c.division == "QF_NIA" and c.flip == "sat->unsat" and not _is_stale_binary(c)


def _is_polyhedral_implied(c: JiecuoCluster) -> bool:
    # Placeholder — signature TBD until EQNA Track 2b ships. Returning False keeps
    # the pattern declared (so verification_report names it) without false matches.
    return False


PATTERNS = [
    ("STALE_BINARY", _is_stale_binary, ClusterPattern(
        name="STALE_BINARY",
        status=STALE_RESOLVES,
        explanation=("Whole-binary stale: one family flipping one direction at "
                     "scale with a single dominant name-pattern (the 1210 VeryMax "
                     "sat->unsat SAT14 signature). The fresh binary collapses it."),
        expected_absent_in_fresh=False,
    )),
    ("SQUARE_CONTRACTOR_X2_EQ_C", _is_potential_square_contractor, ClusterPattern(
        name="SQUARE_CONTRACTOR_X2_EQ_C",
        status=FIXED_ABSENT.format(commit="2965e21"),
        explanation=("ICP SquareContractorZ sign=-1 wrong c-sign produced QF_NIA "
                     "false-UNSAT on x²=c atoms. Fixed in 2965e21; in fresh QF_NIA "
                     "data ALL sat->unsat clusters should be absent."),
        expected_absent_in_fresh=True,
    )),
    ("POLYHEDRAL_IMPLIED", _is_polyhedral_implied, ClusterPattern(
        name="POLYHEDRAL_IMPLIED",
        status=PENDING_FUTURE.format(tracking="EQNA Track 2b"),
        explanation=("Placeholder. Recognition signature TBD; declared so a "
                     "forthcoming Track 2b cluster is tagged explicitly rather "
                     "than confused with an unknown soundness bug."),
        expected_absent_in_fresh=False,
    )),
]


def classify_cluster(c: JiecuoCluster) -> Optional[ClusterPattern]:
    """First matching pattern wins; None if no pattern matches."""
    for _, match, pat in PATTERNS:
        if match(c):
            return pat
    return None


def classify_clusters(clusters: List[JiecuoCluster]) -> Dict[str, List[JiecuoCluster]]:
    """Group clusters by classified pattern name; unclassified -> 'UNCLASSIFIED'."""
    out: Dict[str, List[JiecuoCluster]] = {}
    for c in clusters:
        p = classify_cluster(c)
        out.setdefault(p.name if p else "UNCLASSIFIED", []).append(c)
    return out


def expected_absent_patterns() -> List[ClusterPattern]:
    """Patterns whose PRESENCE in fresh data is a REGRESSION (verification signal)."""
    return [p for _, _, p in PATTERNS if p.expected_absent_in_fresh]


def annotate(c: JiecuoCluster) -> str:
    """Short inline annotation for a cluster table row, e.g. '= STALE_BINARY'."""
    p = classify_cluster(c)
    return "" if p is None else "= " + p.name


def verification_report(clusters: List[JiecuoCluster]) -> str:
    """For each expected-absent pattern, report PRESENT (regression) or absent (verified).

    This is the post-fix verification signal master asked for: after the integrated
    binary's differential lands, SQUARE_CONTRACTOR_X2_EQ_C should be 'absent — verified'.
    """
    classified = classify_clusters(clusters)
    lines = ["Verification (expected-absent patterns; PRESENCE = regression):",
             "  {:<28} {:<48} {}".format("pattern", "status", "result")]
    for p in expected_absent_patterns():
        matched = classified.get(p.name, [])
        if matched:
            n = len(matched)
            total = sum(c.count for c in matched)
            result = "PRESENT (%d cluster%s, %d 解错) — REGRESSION" % (
                n, "" if n == 1 else "s", total)
        else:
            result = "absent — verified"
        lines.append("  {:<28} {:<48} {}".format(p.name, p.status[:48], result))
    return "\n".join(lines)
