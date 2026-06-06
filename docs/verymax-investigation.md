# VeryMax sprint — investigation findings

## Setup

Target: targeted_nia/QF_NIA/20170427-VeryMax/ — 18 nested Farkas-Or
termination-proving cases from Borralleras/Larraz/Oliveras/Rodriguez-Carbonell/Rubio.

```
xolver default : 9 / 18 sat   (all SAT cases solved fast via eager-bb)
xolver default : 0 / 18 unsat (9 UNSAT cases all TO)
z3             : 18 / 18      (uses nlsat, ~30-179 nlsat-conflicts each)
```

The **9 UNSAT cases** are the gap. They're small (26-62 lines), so the
blocker is algorithmic, not size.

## What was found

### 1) Default eager-bb hangs on Farkas-Or UNSAT cases
Verified via `SOLVE_PHASE_PROF=1`: xolver reaches `eager-bb-start` and stays
there until timeout. The bilinear `(* bounded_var λ_var)` monomials with
unbounded `λ` multipliers cause EagerBitBlast's width-search to diverge.

### 2) Disabling eager-bb still doesn't solve
`XOLVER_NIA_EAGER_BITBLAST=0` lets the NIA theory pipeline run but it
still cannot refute. Tried: CDCAC, modular, Groebner — none crack.

Per iter-47 task note: "CDCAC/ICP operate over reals, can't prove integer
UNSAT — algorithmic dead-end". These cases have feasible real-domain LP
relaxation (lambda can be fractional), so CDCAC can't refute. z3 uses
**integer-specific nlsat reasoning** that xolver lacks.

### 3) FarkasOr stage exists and detects correctly
`XOLVER_NIA_FARKAS_OR=1` enables the existing Farkas-Or pipeline. Diagnostic
runs (added temporarily to FarkasOrDetector::detect and stageFarkasOr) show:

```
Detector on loop3 UNSAT case:
  assertions=5   blocks=1   branches=2   outer=3
  bounded=2 (Nl167s^01 ∈ [-2,2], Nl167i^01 ∈ [-2,2])
  unboundedCT=1 (Nl167CT1)
  profile.good() = true

Table builder:
  rows=26 feasibleTotal=26 exhaustive=1 outerEmpty=0
```

So the detector classifies the case correctly AND the table is exhaustive.
The path is set up; just the consumer is wrong.

### 4) The deep bug: `enumerateCsp` collapses rows
```
17-row table → 5 CSP candidates
```

`enumerateCsp` collapses rows that share the same `(B-tuple, branch_idx)`
key, keeping only ONE `lambdaRay` per pair. The other rays are discarded.

For `From_T2__consts4nt` (genuine SAT): 17 feasible rows, 5 candidates
returned, all 5 fail full-formula validation. z3 finds SAT — meaning the
satisfying ray is among the 12 collapsed.

### 5) All-rows fallback STILL doesn't recover SAT
Attempted: bypass `enumerateCsp`, iterate `table.rows` directly, build a
`FarkasOrAssignment` per row, validate. Result: NO row validates either.

Reason: rays are LP-feasible for the BRANCH but don't account for OUTER
assertions. `FarkasOrBranchSolver::solveBranch` builds rays from the
branch's atoms in isolation. Outer assertions add more constraints that
ray values violate. The actual SAT model is a linear combination of rays
plus residual values, not extreme-ray vertices alone.

### 6) Heuristic UNSAT emission is unsound
Attempted: "if all candidates fail validation → emit UNSAT". Found 4 SAT
cases that triggered false-UNSAT (because their ray-set was incomplete OR
their CT pick was wrong).

### 7) Auto-disabling eager-bb when FarkasOr opted-in is harmful
Attempted: when user sets `XOLVER_NIA_FARKAS_OR=1`, skip eager-bb (since
FarkasOr is the right tool). Result: lost 3 SAT cases that eager-bb was
solving correctly.

## What's actually needed

To close the 9-case UNSAT gap, the proper path is one of:

**(A) Per-row LP infeasibility check WITH outer assertions** —
For each (B-tuple, branch) row, substitute the bounded values into ALL
constraints (branch + outer + residual), then run LRA/LIA to check if
the resulting linear system is feasible over (lam, CT, residuals).
If infeasible for every (B-tuple, branch) → UNSAT.

This requires the existing `FarkasOrBranchSolver` to incorporate outer
assertions into its LP — currently it sees only the branch's own atoms.
Substantial refactor (multi-day).

**(B) MCSAT-NIA-equivalent (parallel agent's work)** —
The other agent's MCSAT-NIA implementation is the architectural fix
for this entire class of formulas. Hard problem; right tool.

## Concrete leftover findings

- FarkasOrDetector correctly classifies VeryMax cases.
- FarkasOrSolver's table builder produces exhaustive support tables.
- `enumerateCsp` loses information by collapsing rows on `(B, branch)`.
- `FarkasOrBranchSolver` builds rays from branch-only LP; outer ignored.
- ArithModelValidator is correct (not a bug — actually catches that
  candidates from the table don't satisfy outer assertions).

No code changes shipped from this investigation — every attempt was
unsound or net-negative on the SAT corpus. The investigation IS the
deliverable: it pins which subsystem needs the multi-day work.

## What WAS shipped (prior commits)

The LCTES `.locals` recipe in `docs/lctes-unconstrained-elim.md` and the
UnconstrainedElim infrastructure (commits be12735 .. a39f26c) remain
valuable corpus-cracking work from earlier in the session.

VeryMax gap remains open. Multi-day NRA / MCSAT work owned elsewhere.
