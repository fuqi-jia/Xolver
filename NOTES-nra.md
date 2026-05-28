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

## #11 CAC efficiency — incremental diagnosis (in progress)

Instrumented CAC bail reasons (`XOLVER_NRA_CAC_DIAG` → /tmp/cac_diff.txt +
/tmp/cac_cell.txt). On winnable buildClosure-bound cases (CONVOI2 meti-tarski
z3=unsat; frontier Sturm mbo_E10E17/E12E14), CAC reaches **depth 3 (4-var)** then
bails — exact sub-cause = **`vanish-nonleaf`**: a characterization (discriminant/
resultant/coeff) poly VANISHES at the rational prefix.

**This is McCallum nullification.** Skipping a nullified projection poly at a
non-leaf level is UNSOUND (the lower-dim cell may not stay sign-invariant — the
curtain problem), so CAC correctly **FLOORS to Unknown** (never false-UNSAT;
falls through to Collins). SOUND, just incomplete.

**Sound recovery (the next deep increment):** wire the Lazard **[H3] valuation**
(`lazardEvaluateToUnivariate` — recover the residual via the lowest nonzero
derivative w.r.t. the nullified prefix var) into the CAC rational-prefix path.
It's implemented + wired for ALGEBRAIC-prefix towers (`isolateRealRootsViaTower`)
but not for this rational-prefix nullification. Alternative cheaper mitigation:
generic sample selection at the parent level to avoid landing on a nullification
point (needs recursion-level resampling). Both are non-trivial. This is the SAME
completeness ceiling the Lazard work documented ([[project-lazard]]: nullification
recovery + [H4]). asin-8 (SAT) SPINS separately (not a bail) — likely the
characterization recursion exploring many cells; secondary.

→ CAC's UNSAT completeness on buildClosure-bound families is gated on this
nullification recovery. Floored sound for now; the recovery is a focused
fresh-session effort. Win condition (CAC dominates Collins → unblock task #8) is
NOT yet met.

**WHY Lazard doesn't already cover it (user asked):** Lazard's nullification
recovery IS correct + implemented — but only for the **algebraic-prefix tower**
case: `isolateRealRootsViaTower` runs the [H3] valuation (`lazardEvaluateToUnivariate`,
LibpolyBackend.cpp:1612) ONLY after `if (algCount < 1) return empty;` (line 1556).
My CAC hits nullification at a **pure-rational prefix** (algCount==0), which that
path returns empty for. So it's not a Lazard bug or a wrong Lazard impl — it's a
DISTINCT, unimplemented case (rational-prefix nullification), and CAC correctly
floors (sound). Candidate sound fixes (each needs the per-cell cert + differential
before trusting UNSAT):
  (a) **rational-prefix valuation recovery** — the lowest-order nonzero derivative
      of p w.r.t. the nullified prefix vars along a generic direction (new; the
      0-dim analogue of the tower [H3] valuation).
  (b) **all-coefficients (Collins) single-cell characterization** — emit ALL
      coefficients (not just Lazard's LC/TC) in characterize, so a vanished poly's
      coeffs are in the characterization → skip-on-vanish becomes sound (the
      CdcacCore.cpp:798 Collins argument), still single-cell (not the full
      iterated closure). Cheaper to implement; verify the propagation makes the
      lower covering delineate the sample-on-variety.
  (c) **generic sample selection** — choose the parent samples to avoid landing on
      coefficient varieties (recursion-level resampling); avoids nullification.
Most promising = (b): contained, no new valuation, keeps single-cell. SOUNDNESS-
CRITICAL — gate on per-cell cert + Collins-vs-CAC differential (no false-UNSAT).

**⚠️ SOUNDNESS TRAP (do NOT do this) — two separate semantics, never mixed:**
The Lazard valuation recovers the **lifting boundary / neighbourhood structure**,
NOT the original atom's truth on the exact section. Using the recovered residual
as the atom's residual is UNSOUND. Counterexample (`p=(x-1)·y`, section `x=1`):
`p≡0` on the section, valuation recovers `y`; but `p>0` is ALWAYS FALSE at `x=1`,
so treating `p>0` as `y>0` → false-sat. Therefore:
  - **Atom truth / section satisfiability:** a zero specialization means `p≡0` on
    the section → judge the atom by `p=0` directly (our leaf `signAt` already does
    this: `Sign::Zero` → `relationHolds(Zero,>)`=false). NEVER the valuation.
  - **Lifting boundary / root isolation only:** a zero specialization MAY use the
    valuation to recover boundary polys — but those feed the COVERING/REFINEMENT,
    not the atom. And for the sample-null-but-sector-not-null case, the correct
    action is to introduce the nullification locus (`x=1`) as a refinement
    boundary, NOT to use the derivative as a delineator.
So candidate (a) as "valuation→atom residual" is the trap; the correct (a) keeps
the valuation strictly in the lifting/refinement channel. The current **bail is
sound** and must not be replaced by a naive valuation-as-residual.

**VERIFIED sound on the adversarial nullification cases** (now locked as
nra_142_unsat / nra_143_sat): `(x-1)*y>0 ∧ x=1` → unsat (default/CAC/all-flags,
= z3); `(x-1)*(y-2)=0 ∧ x=1 ∧ y<0` → sat. No false-sat / false-unsat. The leaf
`signAt` handles the section nullification correctly (atom-truth = p≡0).

## ⚠️ CAC false-UNSAT FOUND + floored (2026-05-29)

Running the regression suite with `XOLVER_NRA_CAC=1` exposed **false-UNSAT**:
nra_014/022/047/138 (all `:status sat`) returned UNSAT. Root cause: my
`characterize` uses Lazard's LC/TC set (`lazardProjectStep`), which is INSUFFICIENT
for nullification without the [H3] valuation → the covering is wrongly declared
gap-free → false-UNSAT. (The 12 Sturm-MBO cases I'd sampled were all UNSAT, so they
didn't expose it; the suite's SAT cases did.)

**FLOORED (NraSolver stageCac):** CAC-UNSAT is no longer trusted — on
`CacStatus::Unsat` the stage returns nullopt (defer to Collins, the validated
baseline). CAC keeps only its validated-SAT (sound). This is the user's
"no UNSAT from an unverified characterization" mandate. Re-enable CAC-UNSAT only
with a per-cell certificate. reg ON (CAC=1) now 179/179 (no false-UNSAT).

**THE FIX (cvc5-referenced, `reference/cvc5/.../coverings/cdcac.cpp`):** make
`characterize` SAMPLE-AWARE with McCallum **required coefficients**
(`requiredCoefficientsOriginal`): for poly f, the projection coefficients are
f's var-coefficients TOP-DOWN, adding each, stopping at the first one that is
constant OR **nonzero at the sample** (`SignCondition::NE`). This correctly
delineates the degree-drop / nullification loci at lower levels (sound, no
valuation needed), and is sample-pruned (smaller than full). Plus disc_v(f) and
pairwise res_v(f,g). Replaces the LC/TC-only set that caused the false-UNSAT.
Then re-enable CAC-UNSAT, gated by the adversarial tests (nra_142/143) + a
Collins-vs-CAC differential (0 false-UNSAT on z3-decidable) + per-cell cert.

## ✅ CAC false-UNSAT ROOT-CAUSED + FIXED (2026-05-29)

The false-UNSAT was NOT the covering (CacCovering point-gap at √2 verified correct)
nor (only) the characterization. ROOT CAUSE: the **RealAlg→RealValue→RealAlg
round-trip lost the rootIndex**. `CacEngine::toRealAlg` rebuilt the sample with
`rootIndex=0`, but algebraic `signAt` picks `roots[rootIndex]` (LibpolyBackend
~:1043) — so for √2 (root index 1 of x²-2) it evaluated at **−√2**, making `x>0`
wrongly violated → the SAT point √2 never accepted → covering wrongly gap-free →
false-UNSAT. (Confirmed via a leaf-trace: the √2 point-gap WAS sampled but
mis-evaluated.)

**FIX:** `toRealAlg` now isolates the defining poly's roots and returns the one
whose isolating interval matches the RealValue's — the correct rootIndex + the
backend's native RealAlg. Plus the McCallum required-coefficients in characterize
(completeness). RESULT: nra_014/022/047/138 → sat (was false-unsat); reg ON
(CAC=1 + TRUST_UNSAT=1 + sign-refute) **179/179, 0 false**; adversarial nra_142/143
sound; unit 918/918.

**Promotion gate (still):** CAC-UNSAT remains floored by default
(`XOLVER_NRA_CAC_TRUST_UNSAT` OFF) — the 179 suite is necessary but the user
mandated a **broad z3 differential + per-cell certificate** before trusting UNSAT
(esp. for z3-timeout/frontier cells with no oracle backstop). The fix makes
trust-unsat-mode pass the local suite; run the broad differential
(`XOLVER_NRA_CAC=1 XOLVER_NRA_CAC_TRUST_UNSAT=1`, server) + add per-cell certs to
promote. CAC `XOLVER_NRA_CAC` stays default-OFF until then.

## Queue resolutions (evidence-based)

- **#8 Collins deletion → DECISION: KEEP Collins.** Differential (CAC=1+trust-unsat
  vs default, post-fix): on the buildClosure-bound/frontier families CAC=Collins=TO
  (0-unsound) — CAC still bails at `vanish-nonleaf` on the winnable UNSAT, so it does
  NOT dominate Collins. Re-open only if the vanish-nonleaf recovery + per-cell cert
  land and a broad differential shows CAC ≥ Collins.
- **#11 CAC: false-UNSAT FIXED (soundness done).** Completeness remains: CAC bails at
  `vanish-nonleaf` (rational-prefix nullification) on the hard families. The SOUND
  recovery (skip the nullified poly's var-boundary, relying on the now-propagated
  required-coefficients to delineate the locus at lower levels) is PLAUSIBLE but
  must be gated by a per-cell certificate + broad differential — NOT assumed (the
  user's no-unverified-UNSAT mandate; frontier cells have no oracle backstop).
  Floored sound (trust-unsat default-OFF). The remaining deep increment.
- **#10 subtropical broaden → LOW ROI (deferred):** the measured SAT-gap (meti-tarski)
  is BOUNDED transcendental SAT; subtropical finds only "at-infinity" witnesses. No
  measured family benefits. Sign-refute is Sturm-MBO-specific (cross-family gain 0).
- **#12 RP↔libpoly rebuild → LOW ROI (deferred):** the wall is `buildClosure` (BEFORE
  lifting); `specializeToUnivariate` already substitutes in RP space. Only families
  that REACH lifting would benefit — not the gap families.

## vanish-nonleaf skip experiment (reverted — kept the sound bail)

Tried skipping the nullified non-leaf poly's boundary (Collins skip-soundness via
the now-propagated required-coefficients). Result: reg ON (CAC=1+trust-unsat)
179/179 + adversarial sound, BUT (a) NO measured benefit — CONVOI2 stayed
`unknown` (it bails elsewhere after the skip, so the skip alone doesn't close the
winnable), and (b) frontier-soundness UNVERIFIED (no oracle, no per-cell cert).
Per the no-unverified-UNSAT mandate, REVERTED to the bail (verified sound floor).
The real CAC-completeness path is the per-cell certificate + the deeper recursion
work (why CONVOI2 bails after the skip) — a focused fresh-session effort, not a
speculative skip.

## Cross-family sign-refute reach (it does NOT generalize)

sign-refute gain over default (sample): Sturm-MGC 0, Economics-Mulligan 0,
Uncu 0, Pine 0. → sign-refute is SPECIFIC to Sturm-MBO's all-positive-monomial +
positive-orthant shape. Broadening it cross-family is low-value; the 175 Sturm-MBO
recovery is its scope.

## Dead-ends / negative results

- CAC (conflict-driven single-cell coverings, modules A-C, sound + tested) is NOT
  the lever for sign-definite families like Sturm-MBO — it's doubly-exp there too
  (cvc5 doesn't use CAC for these). Kept default-OFF as reusable infra; promotion
  vs Collins gated on a proper differential (task #8) + the sample-aware
  "required coefficients" characterization (LONG#3).
- `XOLVER_NRA_LIBPOLY_PSC` / `XOLVER_NRA_VARORDER` / `XOLVER_NRA_LINEARIZE`: none
  close Sturm-MBO.

## CAC Lazard-completeness campaign (2026-05-29, cvc5-grounded)

Master directive: "CDCAC + Lazard must be UNCONDITIONALLY complete — no floor."
Worked the CAC single-cell lifting to penetrate algebraic-prefix leaves it used
to bail on. **First meti-tarski frontier case (CONVOI2-chunk-0041) now closes
UNSAT, matching z3.** All default-OFF (XOLVER_NRA_CAC + XOLVER_NRA_CAC_TRUST_UNSAT).

The chain of fixes (each unblocked the next bail site, depth-first):
1. **Algebraic-prefix routing** (12396f4): `vanishesAtPrefix` returns Unknown for
   any algebraic prefix by design and sat IN FRONT of the algebraic-capable tower
   path → unreachable. Demoted it to a rational-only fast path; algebraic prefixes
   route straight to Norm/Tower.
2. **Rational-prefix non-leaf nullification = Lazard residual recovery** (12396f4):
   a nullified projection factor is NOT boundary-free; its valuation residual
   (iterated (xi-ai)-division + substitute = cvc5 `reducePolynomial` for rational
   coords) carries genuine lifting boundaries. cvc5 NEVER skips; skipping enlarges
   the cell → false UNSAT. (Leaf nullified *constraints* still skip — uniform truth
   via signAt → whole fiber excluded.) Bug found: `divideByLinearExact` dropped the
   xi^0 quotient term (`fromVar(v,0,·)` returns zero by design).
3. **No-var skip** (3144ab2): a boundary poly with no `var` dependence after the
   rational coords are fixed has no lift-axis boundary → skip (was bailing
   "p1-no-mainVar" at algebraic leaves).
4. **Conservative-inclusion membership** (3144ab2): the Norm's real roots are a
   sound SUPERSET of p1's real boundaries (every real root of p1's specialization
   is a root of the Norm). On `RootMembership::Unknown`, INCLUDE the candidate
   (extra boundary only refines the covering — splits a sign-invariant region into
   two equally sign-invariant pieces, never merges) instead of bail. Sound +
   complete; replaces bail-on-Unknown that cost completeness for no soundness gain.
5. **Round-trip interval refinement** (3144ab2): `toRealAlg` matched re-isolated
   roots by coarse interval overlap → >1 candidate when the RealValue interval is
   loose. Now refine each candidate (bisect against defining poly) and drop those
   provably disjoint → unique match (true match brackets its root, never dropped);
   still fail-closed if the interval genuinely brackets two roots.

**Validation:** full NRA reg 143/143 OFF + 143/143 ON, unit 920/920, adversarial
nra_142/143 + 4 rootIndex cases all correct. **meti-tarski 150-case differential
vs z3: 0 UNSOUND, 101 solved-agree** (CAC-UNSAT path is sound).

REMAINING cdcac gaps (still floored, SOUND — bail → Unknown, never false-UNSAT):
- `AllDerivativesZero` (Lazard valuation [H3] incomplete reason).
- `towerNorm-not-ok` (degenerate iterated-resultant Norm).
These are deeper tower-kernel limitations; cvc5 sidesteps them with CoCoA Gröbner
reduction over the tower. Tracked for follow-up.

## TODO (LONG-LINE queue)
1. ~~Extend classification to meti-tarski / hycomp / kissing.~~ (done)
2. ~~Broaden subtropical (SAT-gap).~~ (shipped, low-ROI)
3. CAC late-path + UNSAT_CERT: completeness DONE (CONVOI2 closes); per-cell
   certificate for default-on `XOLVER_NRA_CAC_TRUST_UNSAT` still pending (#17).
4. ~~Re-profile + fix CDCAC per-cell RP↔libpoly rebuild.~~ (done)
5. Frontier honesty: quantify the nlsat/MCSAT residual.
