# P2 (BMC detection) + P3 (AProVE early-unknown) — findings

**Lane:** preprocess-deep · **Date:** 2026-06-01 · best-effort, post-P1.
**Verdict: neither is a net-positive preprocessing lever. P1 (GAUSS guard) remains the lane's shipped win.**

## P2 — BMC unrolling structure detection (Dartagnan ReachSafety-Loops)

**The prize is real but not reachable from the frontend.**
- z3 solves the smallest Dartagnan LIA (`terminator_01-O0`, 86 KB) in **1 decision**
  (`decisions=1, propagations=1, added-eqs=129`) — preprocessing-dominated.
- But z3's `simplify` only shrinks the formula **26 %** (86 653 → 64 376 B); the
  speed comes from the **synergy** of `simplify ∘ propagate-values ∘ solve-eqs`
  producing a residual that its engine decides in 1 step — not from collapsing to
  nothing.
- **Hypothesis tested & shipped-then-reverted:** the BMC SSA chains have many
  constant bindings (`last_val_at_memory_i = 0`) and xolver's
  `UnconditionalConstantPropagation` runs **once**, not to fixpoint. Wired a gated
  fixpoint loop (`XOLVER_PP_CPROP_FIXPOINT`) so a propagated constant that turns a
  downstream SSA def into a new constant is re-collected.
  **Result: 0/8 Dartagnan recovered.** The memory cells depend on non-constant
  *conditions* (`ite`), so constant propagation doesn't cascade — the bindings
  don't deterministically chain. Reverted (no unmotivated flag).
- The actual bottleneck (confirmed earlier, gdb): `LiaSolver::assertLit` in the
  `cb_check_found_model` CDCL(T) loop. Even a z3-quality residual would still hit
  xolver's per-model theory re-assertion cost. **This is the lia-lra-deep / NIA
  engine** (incremental theory propagation), not frontend folding.

**Conclusion:** Dartagnan is PP-synergy + engine-bound. Replicating z3's
integrated simplifier is a large lift with uncertain payoff (engine still choke).
Routed to lia-lra-deep (LIA) + NIA. No preprocess-deep lever.

## P3 — AProVE NIA early-unknown

**Score-neutral and risky; not worth shipping.**
- AProVE QF_NIA current state: **1426 timeout** (avg 20.3 s — engine spins the
  whole budget), 953 sat (avg 0.8 s), 30 unsat. The false-SAT class is already
  floored to `unknown` by the default-on NIA validate-sat floor (sound).
- "Detect AProVE pattern + early-unknown" would convert the 1426 `timeout` →
  `unknown` faster, but **`timeout` and `unknown` score identically (0)** in
  SMT-COMP single-query — **no scoring gain**.
- **Risk outweighs it:** any structural early-unknown heuristic that mis-fires on
  a solvable case is a completeness loss (genuine sat/unsat → unknown = score
  loss). The hard gate is "0 genuine solve lost"; a pattern detector cannot
  guarantee that on an undecidable theory. Net-negative expected value.
- The only context where early-unknown helps is a **global/portfolio time budget**
  (free the slot for another arm) — that is the strategy/portfolio lane
  (`ZOLVER_STRAT_PORTFOLIO`), not preprocessing.

**Conclusion:** not a preprocess-deep lever. If pursued, it belongs in the
portfolio scheduler with a strict no-genuine-loss guard.

## Net
- **P1 (GAUSS densification guard) is the lane's shipped, net-positive deliverable.**
- P2, P3 surfaced real structure but are engine-bound / score-neutral — documented,
  not promotion-pushed (per dispatch). Both routed to the appropriate engine lanes.
