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

## Family classification (oracle z3+cvc5 vs our levers, 0-unsound everywhere)

| family | sample | solved | winnable (oracle-fast, we TO) | frontier (all TO) | note |
|---|---|---|---|---|---|
| Sturm-MBO (405) | 51 | 3→**175 w/ sign-refute** | ~210 (all UNSAT) | 21 | sign-refute closes it |
| meti-tarski (7006) | 24 | 15 | **9** | 0 | **highest-ROI gap — all oracle-solvable, NO frontier**; profile needed |
| hycomp (2752) | 19 | 6 | 9 | **4** | 4 frontier = nlsat wall (LONG#5) |
| kissing (45) | 15 | 2 | 2 | **11** | mostly frontier (sphere-packing); low ROI |

→ Next lever: meti-tarski winnable gap (no frontier, so fully achievable). Profile
a winnable case to name the bottleneck (CDCAC lifting? buildClosure? cut-loop?).
hycomp/kissing frontier = the nlsat residual (LONG#5).

## Family: meti-tarski (7006) — winnable gap profiled

Winnable ≈ 37% (9/24 sample), **frontier 0** (z3/cvc5 always solve). The gap is
DOMINATED by `z3=sat, xolver=unknown` (we give up on SATISFIABLE transcendental-
bound cases: asin/atan/sin/cos/exp/sqrt) + some `z3=unsat, xolver=unknown`.
Profiled the spinning SAT case `asin-8-vars4` (4 vars, SAT): SAME wall as
Sturm-MBO — `CdcacCore::buildClosure → projectLevel → determinant` (O(n!)).
`XOLVER_NRA_LIBPOLY_PSC=1` removes the determinant but `asin-8` STILL TO →
**the full Collins closure is doubly-exp in DEGREE** (transcendental approxes are
high-degree), not just the determinant constant-factor.

**Lever for meti-tarski:** NOT a flag flip. The SAT cases need model-construction
(nlsat/MCSAT — assign→check→backjump, no full closure) OR an efficient
single-cell CAC (LONG#3 with the sample-aware "required coefficients"
characterization — my CAC v1's conservative characterization is as expensive as
the full closure, so it doesn't help yet). The UNSAT cases need the same
single-cell projection. Both are LARGE. Note these are NOT "frontier" (z3/cvc5
solve them) — they are a CAPABILITY gap (we lack nlsat + efficient CAC).

## Frontier (LONG#5): genuine nlsat/MCSAT residual

| family | frontier (all-TO incl z3+cvc5) | note |
|---|---|---|
| Sturm-MBO | 21/51 | hard even for cvc5 |
| meti-tarski | 0/24 | NOT frontier — capability gap (need nlsat/efficient-CAC) |
| hycomp | 4/19 | BMC — the recurring nlsat wall (project_nonlinear_sat_strategy) |
| kissing | 11/15 | sphere-packing, intrinsically hard |

→ The TRUE frontier (unreachable without nlsat/MCSAT) is concentrated in hycomp
BMC + kissing. meti-tarski is reachable-but-needs-capability. The single biggest
NRA capability lever remains: **don't build the full Collins closure** (efficient
single-cell CAC) and/or **nlsat model-construction** for bounded SAT.

## Lever ROI re-assessment (after classification — what to do next)

- **Sign-refute (DONE):** the session win — 175/405 Sturm-MBO recovered, 0-unsound,
  default-OFF + in `--allon`. Promote to default after the broad server differential.
- **#8 Collins deletion:** evidence says **DO NOT delete Collins yet** — CAC v1
  bails to Unknown on the hard families (Sturm-MBO, meti-tarski, hycomp) and falls
  through to Collins, so Collins is still the workhorse. Deletion is gated on CAC
  first DOMINATING Collins, which needs the efficient single-cell characterization
  (#11). Differential would just confirm this. LOW priority until #11 lands.
- **#11 efficient single-cell CAC (BIG lever):** the one structural fix that
  addresses the buildClosure doubly-exp wall hit by BOTH Sturm-MBO and meti-tarski.
  Needs the sample-aware "required coefficients" characterization (my CAC v1's
  conservative characterization is as costly as the full closure → no win yet).
  Large + soundness-critical. The highest-value remaining NRA capability.
- **#10 subtropical broadening:** LOW ROI for the measured gaps — meti-tarski SAT
  is BOUNDED (transcendental), subtropical finds only "at-infinity" witnesses.
  Helps only unbounded SAT (rare here). Defer.
- **#12 RP↔libpoly rebuild fix:** LOW ROI now — the wall is `buildClosure` (BEFORE
  the lifting phase); `specializeToUnivariate` already substitutes in RP space.
  Only matters for families that REACH lifting (not the gap families). Defer.
- **nlsat/MCSAT (frontier):** the true unreachable residual (hycomp BMC + kissing)
  + the meti-tarski bounded-SAT capability gap. Largest effort; fresh-session.

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
