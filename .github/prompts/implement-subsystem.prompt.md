---
description: "Implement a NLColver subsystem from plan.md. Use when adding a new src/ component, stubbing an interface, or fleshing out an existing skeleton following the Stage A–K roadmap."
agent: "agent"
argument-hint: "Subsystem name or plan.md section, e.g. 'expr/Rewriter §2.3' or 'sat/CaDiCaL wrapper §4'"
---

# Implement NLColver Subsystem

## Prerequisites

Ensure the SOMTParser frontend submodule is present before reading or modifying parser-related code:

```bash
git submodule update --init --recursive
```

This populates `third_party/SOMTParser/`. If the directory is empty, run this command first.

---

## Context

You are implementing a component of **NLColver**, a research-grade C++17 SMT/OMT solver platform.
The canonical design document is [plan.md](../../plan.md).
Code conventions and architectural invariants are in [CLAUDE.md](../../CLAUDE.md).

**Target subsystem / plan.md section:** $ARGUMENTS

If `$ARGUMENTS` is empty, infer the subsystem from the currently open file.

---

## Step 1 — Read the spec first

Before writing any code:

1. Locate the relevant section of `plan.md` (use the table in CLAUDE.md §"Working on subsystems").
2. Copy the data-structure shapes, interfaces, and invariants **exactly** as described there.
3. Check the "verification criteria" (plan.md §21) for this stage so you know what must pass.

---

## Step 2 — Follow these hard invariants (never break them)

| # | Invariant |
|---|-----------|
| 1 | **Soundness boundary.** `Result::Sat` requires a `ModelValidator` pass. Local-search / MCSAT / bit-blast results are *candidates only*. |
| 2 | **Advisor pattern.** Heuristics flow through `Advisor::propose() → Proposal → policy.accept()`. No heuristic writes solver state directly. |
| 3 | **Three expression views kept separate.** DAG view (`Expr`), Polynomial view (`PolyId`), Evaluation view. Do not collapse them. |
| 4 | **Atomizer boundary.** `AtomId` ≠ SAT variable. `b_i ↔ atom_i` mapping lives in `AtomManager` only. |
| 5 | **CDCL(T) main loop; MCSAT parallel.** `TheorySolver` and `McsatSolver` are distinct interfaces — do not merge them. |
| 6 | **Rewriter is DAG-safe.** Bottom-up + memo table + optional fixpoint. Never naive recursion over shared subterms. |

---

## Step 3 — Code conventions

- Namespace: `namespace nlcolver { ... }` for all library code.
- Typed IDs: `ExprId`, `SortId`, `VarId`, `AtomId`, `PolyId`, `ClauseId`, `ProofId` — all `uint32_t`, defined in `src/expr/types.h`. Null sentinels: `NullExpr`, `NullSort`, etc.
- `pImpl` at public-API boundary (`Solver::Impl`). Keep libpoly / CaDiCaL headers out of `include/`.
- Standard: C++17 only, no GCC-isms, no compiler extensions.
- Containers: prefer `SmallVector<T, N>` (from `src/util/SmallVector.h`) for short child-lists.
- Optional backends: gate CaDiCaL code behind `#ifdef NLCOLVER_HAS_CADICAL`, libpoly behind `#ifdef NLCOLVER_HAS_LIBPOLY`. Provide a stub fallback so builds succeed without them.
- Warnings: code must compile clean under `-Wall -Wextra -Wpedantic`. Only `-Wno-unused-parameter` is whitelisted.
- No new CMakeLists edits needed: `src/CMakeLists.txt` uses `GLOB_RECURSE CONFIGURE_DEPENDS`, so new `.cpp`/`.h` files are picked up automatically.

---

## Step 4 — Deliverables

For each file you create or modify:

1. **Header** (`.h` under `src/<subsystem>/` or `include/nlcolver/`):
   - Forward-declare types; keep includes minimal.
   - Document each public type/function with a one-line comment stating its role.

2. **Implementation** (`.cpp` under `src/<subsystem>/`):
   - Full implementation, or clearly-marked `// TODO(stage-X):` stubs for deferred stages.
   - Include the matching header first, then standard library, then project headers.

3. **Unit test** (`.cpp` under `tests/unit/`):
   - Use doctest (`#include <doctest/doctest.h>`).
   - At minimum: one happy-path `TEST_CASE` and one edge-case / error-path `TEST_CASE`.
   - Test case names must be unique and descriptive.

---

## Step 5 — Self-check before finishing

- [ ] All data structures match the shapes in `plan.md` for this subsystem.
- [ ] No invariant from Step 2 is violated.
- [ ] Code compiles as C++17 with no extension-specific syntax.
- [ ] Optional-backend code is properly gated with `#ifdef`.
- [ ] New files placed in the correct `src/<subsystem>/` directory.
- [ ] At least one doctest test case added or updated.
