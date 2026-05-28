# NRA agent notes (agent/nra-2)

Working log for the QF_NRA push: per-family classification, profiles, lever map,
dead-ends. Soundness gate everywhere: default-OFF flag, SAT=validate / UNSAT=prove,
NRA-family reg 177/177 OFF+ON, 0-unsound.

## Lever map (what closes what)

| Family shape | Right lever | Status |
|---|---|---|
| `vars>0 ∧ g=0`, `g` all-same-sign monomials (sign-definite) | **sign-definiteness refuter** (`XOLVER_NRA_SIGN_REFUTE`) | SHIPPED — closes Sturm-MBO winnable ~0.2s, 0-unsound |
| SAT "at infinity" (unbounded inequality systems) | **subtropical** (`XOLVER_NRA_SUBTROPICAL`) | SHIPPED, validate-gated; broadening = LONG#2 |
| genuinely-CAD UNSAT (algebraic cell structure) | CDCAC (Collins) / CAC | Collins is baseline; CAC built (A-C, default-OFF), not yet beating Collins |
| high-var hard SAT (hycomp BMC) | nlsat/MCSAT | frontier — not built (LONG#5 quantifies) |

KEY LESSON: don't infer the lever from "a fast solver solved it" — check WHICH
solver (z3 vs cvc5 differ hugely) and inspect the instance. Sturm-MBO: z3 TIMES
OUT (general CAD/nlsat), cvc5 fast (sign-definiteness). CAC/Collins both TO.

## Family: 20161105-Sturm-MBO (QF_NRA, 405 cases)

**Shape:** 6 positive reals (`hi>0`, `j2>0`) + ONE high-degree multivariate
polynomial `g = 0`, where **every monomial of `g` has a positive coefficient**
(verified mbo_E11E23: 0 subtractions). So `g` = sum of strictly-positive terms
⇒ `g > 0` ⇒ `g = 0` is UNSAT by a trivial O(#monomials) sign argument.

**Oracle classification (51-case stride sample, z3+cvc5 @20s):**

| bucket | count | note |
|---|---|---|
| xolver solves (default) | 3 | trivial ones |
| WINNABLE (oracle definite, we TO) | 27 | **all UNSAT**; cvc5 often <0.5s; z3 TO |
| frontier (all-TO incl. cvc5) | 21 | even cvc5 can't |

→ ~210/405 winnable, **100% UNSAT**. Subtropical (SAT-side) does NOT help.

**Profiles (gdb, Release symbols, launch-under-gdb + SIGINT-to-inferior;
ptrace-attach + perf both blocked on WSL):**
- Collins default: `CdcacCore::buildClosure → ProjectionClosure::projectLevel →
  principalSubresultantCoefficients → determinant` (O(n!) cofactor expansion).
- `XOLVER_NRA_LIBPOLY_PSC=1` removes the determinant (→ libpoly `lp_polynomial_psc`)
  but STILL TO — bottleneck is the full projection CLOSURE (doubly-exp on 6 vars),
  not the per-PSC op. Every var-ordering flag combo also TO.
- `XOLVER_NRA_CAC=1`: CAC returns Unknown (can't decide these) → falls through to
  Collins → the 12s is Collins (gdb confirmed buildClosure). CAC v1 is sound but
  not a Collins replacement here.
- `XOLVER_NRA_LINEARIZE=1`: also TO.

**Resolution — `XOLVER_NRA_SIGN_REFUTE` (SHIPPED, 897cf16):** 12/12 sampled
winnable cases → UNSAT in 0.13–0.57s, **0 unsound**. **Broad 405-case recovery
(SIGN_REFUTE=1, 4s): 175 → UNSAT, 0 sat, 0 unsound, 230 remain TO** (not
sign-definite / frontier). 175 previously-timing-out cases recovered by one cheap
sound check (≈ the ~210 winnable estimate, minus those needing >4s or not
all-same-sign).

## Dead-ends / negative results

- CAC (conflict-driven single-cell coverings, modules A-C, sound + tested) is NOT
  the lever for sign-definite families like Sturm-MBO — it's doubly-exp there too
  (cvc5 doesn't use CAC for these). Kept default-OFF as reusable infra; promotion
  vs Collins gated on a proper differential (task #8) + the sample-aware
  "required coefficients" characterization (LONG#3).
- `XOLVER_NRA_LIBPOLY_PSC` / `XOLVER_NRA_VARORDER` / `XOLVER_NRA_LINEARIZE`: none
  close Sturm-MBO.

## TODO (LONG-LINE queue)
1. Extend classification to meti-tarski / hycomp / kissing (this file's tables).
2. Broaden subtropical (SAT-gap).
3. CAC late-path + UNSAT_CERT (UNSAT-gap, per-cell certs).
4. Re-profile + fix CDCAC per-cell RP↔libpoly rebuild in RP space.
5. Frontier honesty: quantify the nlsat/MCSAT residual.
