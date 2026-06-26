# `theory/arith/` — arithmetic theory solvers

Two groups separate the **per-logic decision procedures** from the **shared
engines** they build on, so it's clear at a glance which directories are
solvers and which are reusable infrastructure:

```
logics/   per-logic decision procedures
  nra/   nonlinear real        nia/   nonlinear integer
  lra/   linear real           lia/   linear integer
  dl/    difference logic (IDL + RDL)
  mixed/ mixed int/real (NIRA + LIRA)

kernel/   engines shared across the logics above
  poly/      polynomial kernel      interval/   interval arithmetic
  linear/    linear-form algebra    linearizer/ nonlinear → linear cuts
  presolve/  preprocessing passes   bit_blast/  bounded → SAT encoding
  icp/       interval contraction   search/     candidate-model search
  refute/    sign/definiteness      integer/    integer reasoning
```

At this root: `ArithSolverBase.{h,cpp}` (the common base for the per-logic
solvers) and `Reasoner.h` (the staged-reasoner interface). The rest of this
document describes that base.

## Shared base: `ArithSolverBase`

`ArithSolverBase.{h,cpp}` is the common base for **all 8** arith solvers.
It consolidates the lifecycle boilerplate that was previously copy-pasted
across them:

- **The assignment trail.** `state_.trail` is a
  `vector<ActiveAssignment>` (`{level, lit, atom, value}`). Before the
  unification, an identical `struct ActiveAssignment` + `activeAssignments_`
  vector was duplicated in 5 solvers.
- **Scope counters and `currentLevel`.**
- **An optional level-tagged pending slot** (`state_.pending`) with
  `recordPending` / `hasPending` / `drainPending` helpers, for solvers
  whose deferred verdict fits a single Conflict/Lemma/Unknown.

`push`, `pop`, `backtrackToLevel`, and `reset` are **finalized** in the
base; subclasses customize via hooks:

| Hook | When |
|---|---|
| `onAssertLit` | after the base records the assignment on the trail |
| `onBacktrack(level)` | after the base rolls the trail/pending back by level |
| `onReset` | after the base wipes `state_` |
| `onPush` / `onPop(n)` | scope notifications (optional) |

`assertLit` is **virtual, not final**: most solvers use the base default
(dedup-by-satVar insert into `state_.trail`), but solvers with a different
admission policy override it (NIA uses an `ActiveLiteralSet` + opposite-
polarity detection; LRA/LIA/NRA keep their own simplex/cursor trail and
override `assertLit` to drive that instead of `state_.trail`).

## The reasoner pipeline: `Reasoner`

`Reasoner.h` defines the stage interface for a solver's `check()`:

```cpp
virtual std::optional<TheoryCheckResult> run(TheoryLemmaStorage&, TheoryEffort);
```

- `std::nullopt` → **continue** to the next stage.
- a `TheoryCheckResult` → **stop** with that verdict (Conflict/Lemma/
  Unknown, or **Consistent** meaning "the theory state is consistent, stop
  here" — not "continue").

This `optional` distinction faithfully models the old linear `check()`
bodies, where every `return consistent()` meant "stop, done", never
"continue".

`ArithSolverBase::check()` is the default: it drains any pending result,
then walks `reasoners_` in order, returning the first non-`nullopt`
verdict (else `Consistent`). A debug assertion guards that no reasoner
mutates the shared trail.

`CallbackReasoner` is a `std::function`-backed `Reasoner` so a solver can
decompose `check()` into named stages (lambdas capturing `this` and
calling per-stage methods) without a subclass per stage. A solver
registers its stages in its constructor:

```cpp
reasoners_.push_back(std::make_unique<CallbackReasoner>(
    "nia.univariate",
    [this](TheoryLemmaStorage& db, TheoryEffort e) { return stageUnivariate(db, e); }));
```

Solvers currently decomposed into reasoner stages: **NRA** (2: presolve,
cdcac), **NIA** (15: 10 engine-wrapping + 5 glue), **LRA** (1: core),
**LIA** (1: core). NIRA/LIRA/IDL/RDL keep a custom `check()` override
(they are thin or dispatch-only).

## Per-theory directory convention

Each theory subdirectory (`lra/`, `lia/`, `nra/`, `nia/`, …) follows this
layout where the pieces exist:

| Subdir | Holds |
|---|---|
| `<Theory>Solver.{h,cpp}` | the facade: lifecycle hooks + reasoner registration |
| `core/` | core data types (normalized constraints, domain store, atom records) |
| `preprocess/` | theory-specific normalizers / preprocessors (e.g. `nia/preprocess/NiaNormalizer`) |
| `reasoners/` | `Reasoner`-shaped engines and the per-engine reasoning steps |
| `engine/` | low-level engines not shaped as reasoners (e.g. NRA CDCAC internals) |
| `backend/` | external-library shims (e.g. NRA's libpoly binding) |

Not every theory has every subdir — only `nra/` is fully populated today.
New passes should land in the matching subdir so they are findable by
path.

Cross-cutting linear utilities shared by LRA/LIA/LIRA/NIRA live in
`linear/` (e.g. `LinearConstraintNormalizer`, `LinearAtomManager`), not in
any single theory's directory.

## Build note

`src/CMakeLists.txt` uses `file(GLOB_RECURSE … CONFIGURE_DEPENDS)` over
each subsystem directory, so new/moved `.cpp`/`.h` files under
`theory/arith/` are picked up automatically — no CMake edits needed when
adding a reasoner or moving a normalizer.
