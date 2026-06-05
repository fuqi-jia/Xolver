# Ultimate NIA / UFNIA / div-mod / EUF+NIA Roadmap

This document captures the user-provided architectural roadmap for the final
solution to LCTES / Dartagnan / leipzig clusters. It is the authoritative
multi-month plan; this branch (agent/nia-bb-3) implements pieces incrementally.

## Current state (iter-76)

- xolver div0/mod0 EUF semantics validated against z3/cvc5 on 6/6 litmus tests
- LCTES F1: real gap (z3 409ms, xolver 85s TO)
- LCTES F2: objectively very hard (z3 + cvc5 BOTH TO at 60s)
- leipzig term-unsat-01: pure NIA, 0 div/mod (z3 74ms, xolver TO/OOM)
- Dartagnan: same EUF+NIA combination root cause as LCTES F1
- ModularResidueReasoner already exists for `mod 2^k` (default-ON)

The user's analysis is correct: it is NOT a soundness problem. The
QF_NIA→QF_UFNIA promotion at div/mod lowering is the standard SMT-LIB
treatment, matching z3 and cvc5. The remaining gap is performance and
NIA-reasoner depth.

## Architecture

```
Frontend / Atomizer
  ↓
Canonical Arithmetic Layer        ← Step 1 (= task #32)
  ↓
DivMod Totalization Layer         ← Step 3
  ↓
EUF + Arithmetic Shared-Term Layer ← Step 2 + Step 4
  ↓
NIA Core Refuter / Model Finder   ← Step 5/6
  ↓
SAT-level lemma / conflict / model
```

## Cluster routing

| Cluster   | Problem                              | Final fix                                                                            |
| --------- | ------------------------------------ | ------------------------------------------------------------------------------------ |
| LCTES F1  | div/mod + EUF+NIA combination slow   | Step 3 DivModPair + Step 4 shared equality + Step 5 modular refuter                  |
| LCTES F2  | objectively very hard (z3/cvc5 TO)   | Same as F1 + bounded memory + portfolio + explainable unknown                       |
| leipzig   | pure NIA OOM/unknown                 | Step 1 canonical poly + Step 5 modular refuter + Step 6 sparse equality elimination |
| Dartagnan | EUF+NIA combination                  | Step 2 numeric UF purification + Step 4 bidirectional equality propagation          |

## Implementation order

### Step 1 — Canonical Arithmetic Layer (= task #32)

Expr → canonical Polynomial; Atom → ArithAtomKey (poly, rel, domain).
arithmetic atom dedup by canonical form, not raw ExprId.

Acceptance:
  `(x+1)^2 = x^2+2x+1` collapses to one atom
  `2x+2=0  =  x+1=0` collapses to one atom
  `x<0 (Int) = x<=-1` collapses to one atom

Status: owned by a separate agent (Atomizer poly-canonical).

### Step 2 — Shared numeric term layer

All Int/Real sort UF / array select / div0 / mod0 purified into ArithVars.
Equality enters BOTH EUF and ArithmeticTheory.

Acceptance:
  `(= (* x y) (select A i))` puts row `x*y - u_select_A_i = 0` into NIA.
  rows=0 no longer happens when equality is between numeric UF terms.

Status: Purifier exists but coverage incomplete for div0/mod0 + multi-theory.

### Step 3 — DivModPair lowering

Each `(div x y)` and `(mod x y)` shares a `DivModPair{q, r, div0, mod0, y_eq_0, y_gt_0, y_lt_0}`.
Guarded branches:
  `g0  => q = div0(x,y), r = mod0(x,y)`
  `gp  => x = y*q + r, 0 <= r, r <= y - 1`
  `gn  => x = y*q + r, 0 <= r, r <= -y - 1`

Activate the branch matching the divisor's proven sign.
`XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO=1` kept as DIAGNOSTIC unknown flag only
(cannot return unsat when divisor not proven non-zero).

Acceptance:
  6 div0/mod0 litmus tests stay green
  symbolic divisor never returns unsat unsoundly
  nonzero divisor propagates remainder bounds quickly

### Step 4 — EUF+NIA combination blackboard

```
checkCombination():
  loop:
    changed = false
    changed |= euf.propagateCongruence()
    changed |= arith.importEufMerges()
    changed |= arith.propagateBoundsCongruences()
    changed |= divmod.activateKnownBranches()
    changed |= euf.importArithEqualities()
    changed |= euf.importArithDisequalities()
    changed |= nia.runRefuters()
    if conflict: return UNSAT
    if not changed: break
  ...validate, split, return verdict
```

EUF merges → arith equalities. Arith equality/disequality → EUF.
DivMod branch facts → both sides. All facts carry reason DAGs.

### Step 5 — NIA modular / finite-field refuter

For each polynomial system, schedule small moduli (2, 3, 4, 5, 7, 8, 9, 16, 32)
and reduce constraints `mod p`. Search finite residue space. If no
satisfying residue exists, original is UNSAT with modular certificate.

For equality-heavy systems, lift to F_p polynomial ideal + lightweight
Groebner-lite. Certificate: `Σ h_i * f_i ≡ 1 (mod p)`.

Status: ModularResidueReasoner exists for `mod 2^k`. Needs extension to
small-prime schedule for general NIA UNSAT (leipzig-class).

### Step 6 — NIA sparse equality elimination

Affine/Gauss elimination over sparse rationals. gcd feasibility.
Unit-coefficient substitution. Sparse row reduction.

Term-count guard so substitution doesn't blow memory.

### Step 7 — Model validation

All `sat` reconstructs div/mod values + div0/mod0 UF interpretation +
EUF classes, then evaluates original SMT formula exactly. No model
returned without validator pass.

## DO-NOT list

- Don't delete div0/mod0 tokens to fake closure
- Don't assume divisor != 0 by default
- Don't treat QF_NIA → UFNIA internal promotion as a bug
- Don't let equality enter only EUF (must enter NIA too)
- Don't continue Gauss when NIA rows=0 due to equality landing in EUF
- Don't use bit-blast budget as a substitute for div/mod reasoning
- Don't return sat/unsat when modular search has no conclusive result
- Don't let substitution expand into OOM
