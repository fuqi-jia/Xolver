# Track A: Native ModEqConst Reasoner

## Goal

Recover LCTES F1 (and any case with `(mod x y) = c` where y is a variable)
WITHOUT eagerly materializing `q*y` (which the lowerer currently does and
which produces a nonlinear constraint NIA cannot decide within budget).

## Architecture

```
parser → preprocess → atomizer → SAT → NIA pipeline
                                          ↑
                                          ModEqConstReasoner (new)
```

The lowerer is intercepted at the assertion level for the shape
`(= (mod a b) c)` (or symmetric). For these:
- Register `ModEqConstFact{x=a, y=b, c, reason}` in the NIA solver.
- DO NOT call `emitVariableDivisorConstraints` (which would emit `q*y`).
- The remainder variable `r` is still introduced in CoreIR (so other
  expressions referencing `(mod a b)` still type-check).
- A new reasoner stage `stageNativeModEqConst` runs BEFORE the legacy
  modular/Hensel path and emits propagations from facts.

Gated by `XOLVER_NIA_NATIVE_MODEQCONST` (default-OFF).

## Phases

### Phase 1.1 — Foundation (this iter)

Files:
- `src/theory/arith/nia/reasoners/ModEqConstFact.h`: struct
- `src/theory/arith/nia/NiaSolver.{h,cpp}`: storage + registration API
- `src/frontend/preprocess/IntDivModLowerer.{h,cpp}`: detection +
  flag-gated skip of variable-divisor constraint emit
- `tests/unit/test_mod_eq_const_fact.cpp`: detection + storage tests

Acceptance:
- Detection finds `(= (mod x y) c)` and registers a fact.
- Flag default-OFF preserves old behavior bit-for-bit.
- Flag ON: variable-divisor constraints NOT emitted for matched shapes.
- All existing regression suites pass.

### Phase 1.2 — Sign/bound mining (next iter)

Implement rules 1-3:
- Rule 1: `c < 0` → only `y = 0` branch viable.
- Rule 2: `y > 0` provable → `y >= c+1`.
- Rule 3: `y < 0` provable → `y <= -c-1`.

Sound: each rule emits Conflict only when bounds genuinely refute, or
DomainUpdated only when bounds genuinely narrow.

### Phase 1.3 — Large-divisor collapse (rule 4)

If `|y| > |x-c|` (interval bounds), derive `x = c`.

### Phase 1.4 — Constant divisor specialization (rule 7)

If `y` is provably constant `k != 0`, route to existing
ModularResidueReasoner with `(x mod |k|) = c % |k|` and skip the
q-quotient path entirely.

### Phase 1.5 — Lazy quotient materialization

Only when all cheap rules saturate AND a downstream stage explicitly
requests the quotient (e.g. for finite-domain enumeration), emit
`x = y*q + c` with sign constraint. Until then keep as `Divides(y, x-c)`.

## Soundness invariant

- Each rule is sound (UNSAT-only on Conflict, narrowing-only on
  DomainUpdated).
- Flag default-OFF means zero behavior change.
- When skipping variable-divisor emit, the modSimpleTest litmus tests
  (6 div0/mod0 cases) MUST still match z3/cvc5 — proof by the existing
  XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO mechanism, which we extend.

## Out of scope (defer)

- Multi-mod-per-divisor inference chains.
- Mod-mod interaction (e.g. `(mod x y_1) = (mod x y_2)`).
- Nesting (`(mod (mod x y) z)`).

These can come in Track A Phase 2+.

## Targets

| Case | Status | Track A intent |
|---|---|---|
| LCTES/digital-stopwatch.locals | TO @ 15s | unsat via rules 1-3-7 |
| LCTES/digital-stopwatch.locals.nosummaries | TO @ 15s | unsat via rules 1-3-7 |

If Phase 1.1-1.4 close both LCTES cases, that's +2 corpus delta — first
real movement since iter-79.

---

## Status (Track A Phase 1.1-1.4 shipped, LCTES still TO)

### What landed
- Phase 1.1 (`38c11d6`): foundation, fact capture in IntDivModLowerer
- Phase 1.2 (`63f3d86`): standalone ModEqConstReasoner + 8 unit tests
- Phase 1.3 (`f2889c8`): NiaSolver plumbing — facts flow lowerer →
  Solver::Impl → NiaSolver::setModEqConstFacts → stageNativeModEqConst
- Phase 1.4 (`ab519f7`): rule 4 (large-divisor collapse) + rule 7
  (constant divisor) + 5 more unit tests (13 total, 26 assertions)

### What stalled — LCTES F1 still TO @ 30s

Targeted experiment results:

  Default                    : unknown @ 113ms (lowerer bails: needsEUF)
  XOLVER_PP_AUTO_EUF_PROMOTE :  TO @ 19s
  XOLVER_NIA_NATIVE_MODEQCONST: unknown @ 99ms (lowerer still bails)
  All Phase 1.4 flags         : TO @ 30s

Pin: my native reasoner registers the facts AND runs in the pipeline,
but its rules require *interval bounds* on y (or both x and y for
Rule 4). The LCTES variables `x_unnamed_*` are unbounded at parse
time — only the legacy q*y emit produces interval-discoverable
constraints, by which point budget is gone.

### What's needed for Phase 1.5 (NOT shipped this session)

The user's design doc calls for:
- Skip emitVariableDivisorConstraints when the fact is captured
- Keep only the equation `(= r c)` as the SAT-level constraint
- Rely on native reasoner to derive sound Conflict/DomainUpdated
- Optionally materialize q*y lazily if no decision after rules saturate

Risk: dropping q*y means the SAT layer can't validate models — a
SAT verdict from the existing engines becomes UNSOUND because we
never connected `r` to `(mod x y)` arithmetically.

The minimum sound version of Phase 1.5 requires either:
1. A validator-side check (after model is found, re-evaluate the
   ModEqConstFact: model satisfies `(x mod y) = c`? If not, reject
   model and keep searching), OR
2. Lazy q materialization on demand (when a stage explicitly asks
   the lowerer to re-emit the q*y branch for a specific def, the
   lowerer regenerates the constraint and the SAT layer continues).

Both are substantial refactors of the lowerer/validator interface
beyond a single cron-round session.

### Honest assessment

Track A Phase 1.1-1.4 shipped real foundation + reasoner + 13/13
unit tests + zero corpus regression. The LCTES gap remains because
the cheap rules need interval data the existing pipeline doesn't
make available before its budget expires.

For real LCTES progress, the next step is either:
- (a) Phase 1.5 with validator-side soundness gate (1-2 day refactor)
- (b) A pre-NIA bound-inference pass that pre-computes y intervals
      from asserted constraints before the q*y emit, so the native
      reasoner can fire on the FIRST pipeline call (less risky)

Both are out of scope for the per-iter cron loop. Track A's value-add
on the corpus is therefore deferred until one of those is built; the
infrastructure already shipped sets the table for either approach.
