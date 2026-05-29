"""eval.flags — the XOLVER_* strategy space for the offline autotuner.

The strategy space is OUR env flags (not Z3 tactics). Names mirror the live
integrated tree (origin/integration) `getenv("XOLVER_*")` calls, so the autotuner
never emits a dead/superseded/no-op flag. Three disjoint buckets:

  SOUNDNESS_FLOORS  — pinned ON in EVERY candidate. The search only toggles
                      OPTIMIZATION_FLAGS, so it cannot produce a floor-off config.
  SOUNDNESS_GATED   — soundness-touching, MASTER-controlled. Never pinned, never
                      toggled by the search (candidate_env refuses them). They
                      stay gated until master decides — NOT autotuner levers.
  OPTIMIZATION_FLAGS — live boolean completeness/perf levers the search explores.
                      Kept all-on-testable this round; master collapses the
                      differential-proven ones into default in one pass later.

Excluded entirely (not 0/1 levers): *_DIAG / *_DUMP* / *_MS / *_BUDGET* /
*_MAX* / *_EVERY numeric+diagnostic envs, *_NO_* disable switches,
XOLVER_NRA_PROJECTION (value not bool), and the STRAT_PORTFOLIO meta-knobs.

Policy: one capability = one flag (no flag per micro-change).
Python 3.6+ / stdlib only.
"""
from typing import Dict, List

# Pinned ON in every candidate (the soundness floors named in the Agent E charter).
SOUNDNESS_FLOORS: List[str] = [
    "XOLVER_PP_STRICT_VALIDATION",
    "XOLVER_PP_VALIDATE_NONLINEAR_SAT",
    "XOLVER_SAT_DEFER_EARLY_CONFLICT",
    "XOLVER_COMB_SAT_FLOOR",
    "XOLVER_NRA_UNSAT_CERT",
]

# Soundness-touching, master-controlled. Stay gated; never enter a candidate.
SOUNDNESS_GATED: List[str] = [
    "XOLVER_ARRAY_COMB_VALIDATE_SAT",
    "XOLVER_NRA_CAC_TRUST_UNSAT",
]

# Live boolean optimization/completeness levers (mirror origin/integration).
OPTIMIZATION_FLAGS: List[str] = [
    # combination  (COMB_ARRAY_NIA is a known net-regression — kept so the
    # promotion gate REJECTS it on zero-gain+worse-PAR2, not silently dropped)
    "XOLVER_COMB_ARRAY_NIA", "XOLVER_COMB_CAREGRAPH", "XOLVER_COMB_MODEL_BASED",
    "XOLVER_COMB_SCALAR_BACKFILL", "XOLVER_COMB_UFARG_ARRANGE",
    # decision heuristics
    "XOLVER_DECIDE_PROBE", "XOLVER_LRA_DECIDE",
    # LIA / LRA
    "XOLVER_LIA_CUTS", "XOLVER_LIA_REPAIR",
    "XOLVER_LRA_BOUND_AXIOMS", "XOLVER_LRA_PIVOT_HEUR", "XOLVER_LRA_PROP",
    # NIA  (MODULAR L3 + LOCALSEARCH WalkSAT = the recovery levers; DIVISOR_FACTOR
    #       supersedes the old DIVISOR_CAP)
    "XOLVER_NIA_REFUTE", "XOLVER_NIA_GCD", "XOLVER_NIA_ICP", "XOLVER_NIA_CDCAC",
    "XOLVER_NIA_BV_CASCADE", "XOLVER_NIA_BITBLAST_FAST", "XOLVER_NIA_DIVISOR_FACTOR",
    "XOLVER_NIA_UNIVARIATE_FULL", "XOLVER_NIA_PRESOLVE_FULL", "XOLVER_NIA_MODULAR",
    "XOLVER_NIA_LOCALSEARCH",
    # NRA  (CAC engine; SUBTROPICAL = SAT-fast front door; SIGN_REFUTE)
    "XOLVER_NRA_CAC", "XOLVER_NRA_LAZARD_LIFT", "XOLVER_NRA_LIBPOLY_PSC",
    "XOLVER_NRA_VARORDER", "XOLVER_NRA_VARORDER_SIMPLEX", "XOLVER_NRA_HYBRID",
    "XOLVER_NRA_PREELIM", "XOLVER_NRA_LINEARIZE", "XOLVER_NRA_SIGN_REFUTE",
    "XOLVER_NRA_SUBTROPICAL",
    # preprocessing / presolve
    "XOLVER_PP_REWRITE", "XOLVER_PP_SOLVE_EQS", "XOLVER_PP_PG_CNF",
    "XOLVER_PP_LET_ELIM", "XOLVER_PP_VALIDATOR_MEMO",
    "XOLVER_PRESOLVE_DEDUP_ROWS", "XOLVER_PRESOLVE_IIS", "XOLVER_REAL_DIV_PURIFY",
    # arrays
    "XOLVER_AX_EXT_WITNESS_COMPLETE", "XOLVER_AX_ROW2_CONST",
    # SAT / strategy
    "XOLVER_SAT_LEMMA_MGMT", "XOLVER_SAT_MIN", "XOLVER_STRAT_PRESETS",
    # UF
    "XOLVER_UF_DISEQ_WATCH", "XOLVER_UF_FAST_CC",
]

# Applied to every logic in flags_for_logic (preprocessing / SAT / strategy /
# global heuristics that aren't tied to one arithmetic theory).
_UNIVERSAL = [
    "XOLVER_PP_REWRITE", "XOLVER_PP_SOLVE_EQS", "XOLVER_PP_PG_CNF",
    "XOLVER_PP_LET_ELIM", "XOLVER_PP_VALIDATOR_MEMO",
    "XOLVER_SAT_LEMMA_MGMT", "XOLVER_SAT_MIN", "XOLVER_STRAT_PRESETS",
    "XOLVER_DECIDE_PROBE", "XOLVER_PRESOLVE_DEDUP_ROWS", "XOLVER_PRESOLVE_IIS",
    "XOLVER_REAL_DIV_PURIFY",
]


def flags_for_logic(logic: str) -> List[str]:
    """The optimization flags plausibly relevant to a logic (stage-1 scoping).

    Imperfect by design — extra flags just get measured and discarded in
    combine(); missing a flag only narrows the search. Universal flags always
    apply.
    """
    name = logic.upper()
    sel = set(_UNIVERSAL)

    def add_prefix(prefix):
        sel.update(f for f in OPTIMIZATION_FLAGS if f.startswith(prefix))

    has_nia = "NIA" in name or "NIRA" in name
    has_nra = "NRA" in name or "NIRA" in name
    has_lia = "LIA" in name or "LIRA" in name or "IDL" in name
    has_lra = "LRA" in name or "LIRA" in name or "RDL" in name
    has_array = name.startswith("QF_A") or "AX" in name
    is_comb = ("UF" in name) or name.startswith("QF_A") or "AUF" in name or "DT" in name

    if has_nia:
        add_prefix("XOLVER_NIA_")
    if has_nra:
        add_prefix("XOLVER_NRA_")
    if has_lia:
        add_prefix("XOLVER_LIA_")
    if has_lra:
        add_prefix("XOLVER_LRA_")
    if has_array:
        add_prefix("XOLVER_AX_")
    if is_comb:
        add_prefix("XOLVER_COMB_")
        add_prefix("XOLVER_UF_")
    return sorted(sel & set(OPTIMIZATION_FLAGS))


# Precomputed for the competition-relevant logics.
_LOGICS = [
    "QF_NIA", "QF_NRA", "QF_NIRA", "QF_LIA", "QF_LRA", "QF_LIRA",
    "QF_IDL", "QF_RDL", "QF_UF", "QF_UFLRA", "QF_UFLIA", "QF_UFNIA",
    "QF_UFNRA", "QF_ANIA", "QF_AUFNIA", "QF_UFDTNIA",
    "QF_AX", "QF_ALIA", "QF_ALRA", "QF_AUFLIA", "QF_AUFLRA",
]
LOGIC_FLAGS: Dict[str, List[str]] = {lg: flags_for_logic(lg) for lg in _LOGICS}

_GATED = set(SOUNDNESS_GATED)


def candidate_env(selected_flags: List[str]) -> Dict[str, str]:
    """Build the env for one candidate config: all soundness floors ON, plus the
    selected optimization flags ON. Floors are always present; soundness-gated
    flags are refused (master-controlled), so the search can never set one."""
    env: Dict[str, str] = {floor: "1" for floor in SOUNDNESS_FLOORS}
    for f in selected_flags:
        if f in _GATED:
            continue
        env[f] = "1"
    return env
