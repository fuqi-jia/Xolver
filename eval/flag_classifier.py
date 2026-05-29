"""eval.flag_classifier — soundness-intent classes for XOLVER_* flags + greedy promoter.

Each optimization flag has a SOUNDNESS-INTENT class that determines how the
autotuner should treat it. Master's framework (and EAGER_BITBLAST's verified
template): a flag's class encodes WHAT IT CAN RETURN, which in turn determines
WHICH GATE applies to its promotion:

  SOUND_SAT_FINDER
    Engine only returns Sat or Unknown (invariant 7: NEVER returns Unsat) AND
    every Sat is validator-confirmed (invariant 1). By design it CANNOT trip the
    解错 gate (false-UNSAT is the dangerous direction; false-SAT is blocked by
    the validator). Promote on net solved-delta > 0; no per-division differential
    re-test is needed (its soundness comes from the engine's invariants, not
    from empirical clearance).
    Template: XOLVER_NIA_EAGER_BITBLAST (Solver.cpp:1176-1198, validator inside
    EagerBitBlastSolver + falls through to CDCL(T) on Unknown).

  UNSAT_PRODUCER
    Engine can return Unsat (refutation/projection/certificate). False-UNSAT is
    the dangerous failure direction — needs the standard --allon differential
    clearance: per division, 0 解错 added vs baseline AND net solved-delta > 0.

  SOUND_PERF_PREPROC
    Doesn't decide; transforms or caches. Sound by design (model recoverable via
    reverse-replay when applicable). No new 解错 should ever appear; promote on
    net >= 0 AND 0 解错 added. Less conservative than UNSAT_PRODUCER because the
    flag has no decision authority.

  CAPABILITY_NUMERIC
    Right action is to tune a value, not flip 0/1 (e.g. a budget in ms or a
    threshold). Excluded from the autotuner's 0/1 search; the registry already
    excludes *_MS / *_BUDGET / *_MAX / *_CAP envs. Declared here so the
    classifier is complete; current membership is empty.

  UNCLASSIFIED
    Default for any flag we haven't audited. Treated like UNSAT_PRODUCER for
    promotion (the conservative side) so the gate always applies.

The class membership below is derived from solver-internals knowledge (invariant
labels in src/, commit messages, and the memory-recorded analyses for each
flag's lane). Sources are cited inline so future audits can verify each entry.

Python 3.6+ / stdlib only.
"""
from typing import Dict, List, Optional

from eval._compat import dataclass
from eval.flags import OPTIMIZATION_FLAGS


# ---- Class identifiers (string constants — 3.6-portable) -------------------- #
SOUND_SAT_FINDER = "SOUND_SAT_FINDER"
UNSAT_PRODUCER = "UNSAT_PRODUCER"
SOUND_PERF_PREPROC = "SOUND_PERF_PREPROC"
CAPABILITY_NUMERIC = "CAPABILITY_NUMERIC"
UNCLASSIFIED = "UNCLASSIFIED"

ALL_CLASSES = (SOUND_SAT_FINDER, UNSAT_PRODUCER, SOUND_PERF_PREPROC,
               CAPABILITY_NUMERIC, UNCLASSIFIED)


# ---- Authoritative classification map --------------------------------------- #
# Citations point at the engine/contract that establishes the soundness intent.
# Anything not listed defaults to UNCLASSIFIED → treated as UNSAT_PRODUCER for
# promotion gating (conservative). Adding a flag here is an explicit audit.

FLAG_CLASS: Dict[str, str] = {
    # SOUND_SAT_FINDER — engine never returns Unsat; Sat is validator-confirmed.
    "XOLVER_NIA_EAGER_BITBLAST": SOUND_SAT_FINDER,   # Solver.cpp:1176 inv 1+7
    "XOLVER_NIA_LOCALSEARCH":    SOUND_SAT_FINDER,   # WalkSAT candidate-only, validator-gated
    "XOLVER_NRA_SUBTROPICAL":    SOUND_SAT_FINDER,   # 1656497 model-validate then fallthrough

    # SOUND_PERF_PREPROC — transforms / caches; no decision authority.
    "XOLVER_NIA_NORM_CACHE":      SOUND_PERF_PREPROC,  # 273e0a3 incremental cache
    "XOLVER_PP_REWRITE":          SOUND_PERF_PREPROC,  # 98d2880 rewriter, oracle-validated
    "XOLVER_PP_SOLVE_EQS":        SOUND_PERF_PREPROC,  # 34ed63a var-elim + reverse-replay
    "XOLVER_PP_PG_CNF":           SOUND_PERF_PREPROC,  # 6964efa Plaisted-Greenbaum CNF
    "XOLVER_PP_LET_ELIM":         SOUND_PERF_PREPROC,  # let-binding elim, syntactic
    "XOLVER_PP_VALIDATOR_MEMO":   SOUND_PERF_PREPROC,  # validator-output memoization
    "XOLVER_PRESOLVE_DEDUP_ROWS": SOUND_PERF_PREPROC,  # row deduplication
    "XOLVER_PRESOLVE_IIS":        SOUND_PERF_PREPROC,  # IIS extraction (presolve)
    "XOLVER_REAL_DIV_PURIFY":     SOUND_PERF_PREPROC,  # 9e41e83 RealDivLowerer purification
    "XOLVER_SAT_LEMMA_MGMT":      SOUND_PERF_PREPROC,  # FIFO lemma cache
    "XOLVER_SAT_MIN":             SOUND_PERF_PREPROC,  # theory-agnostic clause dedup

    # UNSAT_PRODUCER — engine can return Unsat (refutation / projection / cert).
    "XOLVER_NIA_MODULAR":         UNSAT_PRODUCER,    # residue/Hensel UNSAT
    "XOLVER_NIA_REFUTE":          UNSAT_PRODUCER,    # explicit refutation
    "XOLVER_NIA_GCD":             UNSAT_PRODUCER,    # gcd-based infeasibility
    "XOLVER_NIA_ICP":             UNSAT_PRODUCER,    # interval contractor refutation
    "XOLVER_NIA_CDCAC":           UNSAT_PRODUCER,    # CDCAC produces UNSAT cells
    "XOLVER_NIA_BV_CASCADE":      UNSAT_PRODUCER,    # BV-cascade conflict
    "XOLVER_NIA_BITBLAST_FAST":   UNSAT_PRODUCER,    # bit-blast can refute
    "XOLVER_NIA_UNIVARIATE_FULL": UNSAT_PRODUCER,    # univariate reasoner
    "XOLVER_NIA_PRESOLVE_FULL":   UNSAT_PRODUCER,    # full presolve
    "XOLVER_NIA_IFACE_LIFECYCLE": UNSAT_PRODUCER,    # 7fe3ba2 N-O iface backtrack
    "XOLVER_NRA_CAC":             UNSAT_PRODUCER,    # CAC engine with UNSAT cert
    "XOLVER_NRA_LAZARD_LIFT":     UNSAT_PRODUCER,    # Lazard valuation lifting
    "XOLVER_NRA_LIBPOLY_PSC":     UNSAT_PRODUCER,    # libpoly principal sub-res
    "XOLVER_NRA_VARORDER":        UNSAT_PRODUCER,    # variable ordering (affects cert)
    "XOLVER_NRA_VARORDER_SIMPLEX":UNSAT_PRODUCER,    # simplex-guided var order
    "XOLVER_NRA_HYBRID":          UNSAT_PRODUCER,    # hybrid CAC@Full
    "XOLVER_NRA_PREELIM":         UNSAT_PRODUCER,    # variable pre-elimination
    "XOLVER_NRA_LINEARIZE":       UNSAT_PRODUCER,    # linearization arm
    "XOLVER_NRA_SIGN_REFUTE":     UNSAT_PRODUCER,    # sign-based refutation
    "XOLVER_LIA_CUTS":            UNSAT_PRODUCER,    # cuts produce infeasibility
    "XOLVER_LIA_REPAIR":          UNSAT_PRODUCER,    # repair search
    "XOLVER_LRA_BOUND_AXIOMS":    UNSAT_PRODUCER,    # bound axioms
    "XOLVER_LRA_PROP":            UNSAT_PRODUCER,    # LRA Farkas propagation
    "XOLVER_LRA_PIVOT_HEUR":      UNSAT_PRODUCER,    # simplex pivot heuristic
    "XOLVER_COMB_ARRAY_NIA":      UNSAT_PRODUCER,    # known net-regression (kept so gate rejects)
    "XOLVER_COMB_CAREGRAPH":      UNSAT_PRODUCER,    # care-graph + shared-pair prune
    "XOLVER_COMB_MODEL_BASED":    UNSAT_PRODUCER,    # arrangement closure
    "XOLVER_COMB_SCALAR_BACKFILL":UNSAT_PRODUCER,    # typed-channel scalar mint
    "XOLVER_COMB_UFARG_ARRANGE":  UNSAT_PRODUCER,    # UF-argument arrangement
    "XOLVER_DECIDE_PROBE":        UNSAT_PRODUCER,    # decide-probe heuristic
    "XOLVER_LRA_DECIDE":          UNSAT_PRODUCER,    # LRA-guided decide
    "XOLVER_AX_EXT_WITNESS_COMPLETE": UNSAT_PRODUCER,# array extensionality witness
    "XOLVER_AX_ROW2_CONST":       UNSAT_PRODUCER,    # 2-row constant array
    "XOLVER_ARRAY_CONGR_EXT":     UNSAT_PRODUCER,    # array congruence-contrapositive ext
    "XOLVER_STRAT_PRESETS":       UNSAT_PRODUCER,    # 6f504fa strategy presets backbone
    "XOLVER_UF_DISEQ_WATCH":      UNSAT_PRODUCER,    # disequality watch
    "XOLVER_UF_FAST_CC":          UNSAT_PRODUCER,    # fast congruence closure
    "XOLVER_EUF_PROP":            UNSAT_PRODUCER,    # EUF e-propagation
}


def classify_flag(name: str) -> str:
    """Return the soundness-intent class for a flag. Unknown -> UNCLASSIFIED."""
    return FLAG_CLASS.get(name, UNCLASSIFIED)


def coverage_report() -> str:
    """Per-class membership + the registry coverage rate (audited / total opt)."""
    by_class: Dict[str, List[str]] = {c: [] for c in ALL_CLASSES}
    for f in OPTIMIZATION_FLAGS:
        by_class[classify_flag(f)].append(f)
    classified = len(OPTIMIZATION_FLAGS) - len(by_class[UNCLASSIFIED])
    lines = ["Flag-class coverage: %d / %d optimization flags audited (%.0f%%)."
             % (classified, len(OPTIMIZATION_FLAGS),
                100.0 * classified / max(1, len(OPTIMIZATION_FLAGS)))]
    for c in ALL_CLASSES:
        if by_class[c]:
            lines.append("  %s (%d): %s" % (c, len(by_class[c]),
                                            ", ".join(sorted(by_class[c]))))
    return "\n".join(lines)


# ---- Greedy promotion using class-aware gates ------------------------------- #

# Decisions for one (flag, division) pair from a per-flag differential.
PROMOTE_NOW     = "PROMOTE_NOW"        # net>0 + class-gate clears
NEEDS_FULL_DIFF = "NEEDS_FULL_DIFF"    # net>0 but needs broader --allon clearance
REJECT          = "REJECT"             # 解错>0 OR net<=0 with risk
ABSTAIN_TUNE    = "ABSTAIN_TUNE"       # CAPABILITY_NUMERIC — tune value, not 0/1


@dataclass
class FlagStat:
    flag: str
    division: str
    net: int        # solved@1200 candidate - baseline
    jiecuo: int     # ADDED wrong answers under the candidate (cand decided contradicting oracle)
    recovered: int = 0
    regressed: int = 0


@dataclass
class PromotionDecision:
    flag: str
    division: str
    decision: str
    flag_class: str
    reason: str


def decide(stat: FlagStat) -> PromotionDecision:
    """Class-aware promotion decision for one (flag, division) per-flag diff.

    Soundness gate (hard): if jiecuo > 0, REJECT regardless of class — the 解错
    floor never bends. Class then determines what counts as enough evidence:

      SOUND_SAT_FINDER     net > 0 + 0 解错 -> PROMOTE_NOW (class invariants make
                                              broader clearance unnecessary)
      SOUND_PERF_PREPROC   net >= 0 + 0 解错 -> PROMOTE_NOW (no decision authority)
      UNSAT_PRODUCER       net > 0 + 0 解错 -> NEEDS_FULL_DIFF (needs --allon
                                              clearance before default-ON)
      UNCLASSIFIED         treated as UNSAT_PRODUCER (conservative)
      CAPABILITY_NUMERIC   ABSTAIN_TUNE (tune the value, not 0/1)
    """
    cls = classify_flag(stat.flag)
    if stat.jiecuo > 0:
        return PromotionDecision(stat.flag, stat.division, REJECT, cls,
                                 "%d 解错 added — soundness floor blocks" % stat.jiecuo)
    if cls == CAPABILITY_NUMERIC:
        return PromotionDecision(stat.flag, stat.division, ABSTAIN_TUNE, cls,
                                 "tune value, not 0/1")
    if cls == SOUND_SAT_FINDER:
        if stat.net > 0:
            return PromotionDecision(stat.flag, stat.division, PROMOTE_NOW, cls,
                                     "+%d solved; class-invariant: cannot return Unsat" % stat.net)
        return PromotionDecision(stat.flag, stat.division, REJECT, cls,
                                 "net %+d — no benefit" % stat.net)
    if cls == SOUND_PERF_PREPROC:
        if stat.net >= 0:
            return PromotionDecision(stat.flag, stat.division, PROMOTE_NOW, cls,
                                     "%+d solved + 0 解错; no decision authority" % stat.net)
        return PromotionDecision(stat.flag, stat.division, REJECT, cls,
                                 "net %+d regression" % stat.net)
    # UNSAT_PRODUCER + UNCLASSIFIED (treated identically).
    if stat.net > 0:
        return PromotionDecision(stat.flag, stat.division, NEEDS_FULL_DIFF, cls,
                                 "+%d solved; needs --allon differential clearance"
                                 % stat.net)
    return PromotionDecision(stat.flag, stat.division, REJECT, cls,
                             "net %+d — no benefit" % stat.net)


def promote_greedy(stats: List[FlagStat]) -> List[PromotionDecision]:
    """Apply decide() to every (flag, division) FlagStat.

    The "greedy" part is the per-stat independence: each decision is made on its
    own merits, no inter-flag tie-breaking. That's the right shape for now —
    inter-flag interactions need bundle differentials, not per-flag greedy.
    Output is stable-sorted by (decision-priority, -net, flag, division).
    """
    decisions = [decide(s) for s in stats]
    priority = {PROMOTE_NOW: 0, NEEDS_FULL_DIFF: 1, ABSTAIN_TUNE: 2, REJECT: 3}
    stats_by_key = {(s.flag, s.division): s for s in stats}
    decisions.sort(key=lambda d: (priority[d.decision],
                                  -stats_by_key[(d.flag, d.division)].net,
                                  d.flag, d.division))
    return decisions


def format_decisions(decisions: List[PromotionDecision]) -> str:
    if not decisions:
        return "(no per-flag stats supplied)"
    hdr = "{:<32} {:<10} {:<17} {:<19} {}".format(
        "flag", "division", "decision", "class", "reason")
    lines = [hdr, "-" * len(hdr)]
    for d in decisions:
        lines.append("{:<32} {:<10} {:<17} {:<19} {}".format(
            d.flag[:32], d.division[:10], d.decision, d.flag_class, d.reason))
    return "\n".join(lines)
