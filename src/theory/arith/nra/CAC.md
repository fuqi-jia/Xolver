# Conflict-Driven Single-Cell CAC — Design Contract (lever 3)

Status: design pinned (pre-implementation), mirroring `LAZARD.md`. Gated behind
`XOLVER_NRA_CAC` (default OFF). Binding contract; modules MUST conform.

## Why (evidence)

Profiling the QF_NRA `20161105-Sturm-MBO` family (the "251 unsolved-medal"
bucket) showed the bottleneck is **`CdcacCore::buildClosure` — the full Collins
projection closure built upfront**. On a 6-variable, high-degree-equality system
the closure is doubly-exponential: even after removing the O(n!) cofactor
`determinant` (`XOLVER_NRA_LIBPOLY_PSC`) and trying every variable-ordering flag,
all cases still time out. cvc5 closes the same cases in 0.01–0.5 s via
**conflict-driven single-cell coverings** (Ábrahám–Davenport–England–Kremer,
"Deciding the Consistency of NRA with a CDS using Cylindrical Algebraic
Coverings", 2021) — it never builds a full closure; it projects only the
polynomials needed to characterize one cell around the current sample.

Sample classification (51/405 @20 s, z3+cvc5 oracle): xolver solves 3, **27
WINNABLE (all UNSAT, cvc5 often <0.5 s)**, 21 frontier. → ~210/405 winnable.

## Binding invariant (same posture as CDCAC/Lazard)

- **SAT** ⇐ only a full sample that exactly validates all original active
  constraints (model-validated; never trust a heuristic).
- **UNSAT** ⇐ only a complete covering of ℝ at the top level, every interval of
  which carries a single-cell characterization built by a **complete** projection
  operator (Lazard or McCallum-with-well-orientedness-checked). Any incomplete
  characterization / inconclusive root step ⇒ **Unknown, never UNSAT**.
- The CAC path is a **late slow path**: it runs only when the cheap front
  (presolve, subtropical SAT-fast-path) and/or the budgeted Collins pass have not
  decided. Collins/Lazard remain available; CAC never overrides a definite Collins
  verdict.

## Algorithm (get_unsat_cover, recursive)

```
get_unsat_cover(level i, sample s = (x_1=a_1,…,x_{i-1}=a_{i-1})):
  I = []                                   # excluded intervals on the x_i axis
  while ∃ a_i ∈ ℝ not covered by I:
    s' = s ∪ {x_i = a_i}                   # pick a sample point in an uncovered gap
    if i == n:                             # full assignment
       if all active constraints hold at s': return SAT(s')
       cell = single-cell char. of the constraint(s) violated at s'   # 1 poly set
    else:
       r = get_unsat_cover(i+1, s')
       if r == SAT: return SAT
       cell = characterize(r.covering, s')        # project r's polys down to level i
    I.add( interval_from_characterization(cell, a_i) )   # the maximal x_i-interval
  return UNSAT covering = I  (+ the projected polynomial set for the caller)
```

- **Sample selection** picks rationals in uncovered gaps (and algebraic numbers at
  interval endpoints); reuse `RealAlg`/`isolateRealRootsViaNorm` + the existing
  sample machinery.
- **`characterize`** (single-cell projection): the only projection done — over the
  polynomials in the recursion's covering, **specialized at the sample prefix**, so
  they stay low-degree. Built from the **Lazard projection operator** we already
  have (`LazardProjectionOperator`, complete ⇒ no well-orientedness precondition),
  NOT a fresh full closure. This is the soundness-critical core.
- **`interval_from_characterization`** isolates the real roots of the
  characterization polys (at the prefix) bracketing `a_i`, giving the maximal
  sign-invariant interval to exclude. Reuse the tower root-isolation + per-cell
  certificate machinery from the Lazard build.

## Soundness obligations (enforced, not asserted)

1. Every excluded interval's characterization is built by the **complete** Lazard
   operator + a complete root isolation; any `LazardIncompleteReason` /
   `RootComparisonInconclusive` ⇒ abandon CAC for this solve ⇒ Unknown (the
   Collins/Lazard backstop already returns the safe verdict).
2. The top-level covering must be **gap-free over all of ℝ** before returning
   UNSAT (a missed gap = false UNSAT). Track coverage with exact rational/algebraic
   interval arithmetic; an inability to prove gap-freeness ⇒ Unknown.
3. `XOLVER_NRA_UNSAT_CERT` (already present): a CAC UNSAT emits the covering +
   per-interval characterization as the certificate; the replay validator checks
   each interval is sign-invariant and the union covers ℝ.
4. Equational-constraint optimization (designate the single equality, project only
   w.r.t. it) is a **completeness/perf refinement layered later**, behind its own
   sub-gate, with McCallum well-orientedness checked or Lazard-EC obligations met.

## Module plan (A→E), each unit-tested before the next

- **A. Interval/covering data structures** (`nra/cac/Covering.{h,cpp}`): exact
  rational⊕algebraic intervals, gap-finding, gap-free check. Pure, unit-tested.
- **B. `characterize` / `interval_from_characterization`** over the Lazard operator
  (`nra/cac/SingleCellProjection.{h,cpp}`). Unit-tested vs known cells.
- **C. `CacEngine::getUnsatCover`** recursion (`nra/cac/CacEngine.{h,cpp}`),
  SAT=validated / UNSAT=gap-free-covering / else Unknown.
- **D. Wiring**: a `nra.cac` reasoner stage (Full-effort, default-OFF
  `XOLVER_NRA_CAC`) AFTER the budgeted Collins/Lazard pass; getModel reports the
  CAC SAT sample (same pattern as the subtropical stage's `satFastModel_`).
- **E. Differential**: Collins-vs-CAC decided verdicts never disagree; broad
  QF_NRA z3/cvc5 differential 0-unsound; Sturm-MBO winnable-bucket recovered.

## Gate

Default-OFF flag + Unknown guardrail. unit + NRA-family reg 177/177 OFF+ON,
0-unsound. Broad QF_NRA z3/cvc5 differential 0-unsound before promotion (server).
Collins default path byte-identical when the flag is OFF.

## compareRealAlg — certified comparator contract (review-pinned)

Comparing algebraic numbers must NOT "let intervals overlap then keep guessing".
Two separate certificates:
  - EQUALITY certificate: identity / minimal-poly / gcd-membership proof.
  - SEPARATION certificate: refine isolating intervals until DISJOINT.
Invariant: `Less/Equal/Greater` require a mathematical certificate; with none,
return `Unknown` — never guess (no interval-overlap→pick-first, no
budget→assume-equal/distinct, no pointer order as math order).

Steps (in order; first conclusive wins):
1. exact identity — same canonical object id; or same certified minimal poly +
   same rootIndex (different rootIndex on the SAME poly orders directly, no
   refine). Same poly, missing index → locate a UNIQUE root ordinal by interval
   refinement (multiple overlaps → refine; non-unique after budget → Unknown).
2. exact equality — if both minimal and polys differ ⇒ distinct (→ step 3 for
   order). Else g = gcd(defA,defB): deg(g)=0 ⇒ distinct; deg(g)>0 ⇒
   exactRootMembership(g, ·) with priority: (a) minimal-poly divisibility,
   (b) exact signAt(g, root)==0, (c) UNIQUE gcd-root interval membership (count-
   based, never first-overlap). Both belong to the SAME gcd root ⇒ Equal; else
   distinct.
3. certified separation — ONLY after distinctness is proven: refine until the
   isolating intervals are disjoint ⇒ Less/Greater. (Refining possibly-equal
   roots can never separate, so distinctness must be established first.)
4. budget exhausted ⇒ Unknown — do NOT guess.

Caller rules: Unknown must make root isolation / cell construction UNSUPPORTED
(→ Collins fallback), never a pointer/first-overlap order. A non-semantic
stable-key comparator is allowed for map/set keys ONLY, never for cell order /
sign reasoning / covering merge / SAT-UNSAT decisions. To reduce Unknown,
strengthen steps 1/2 (exact equality), do NOT raise the step-3 refine cap.

## Combination-aware CAC — v1 BUILT (default-OFF `XOLVER_NRA_CAC_COMBINATION`)

STATUS (v1, EQNA-paired seam): the NRA side is built behind
`XOLVER_NRA_CAC_COMBINATION` (default OFF, inert until flipped). What it does
when ON, in `NraSolver::stageCac`:
- **Lift** each `interfaceEqualities_`/`interfaceDisequalities_` entry into a
  `CacConstraint` via the SAME `PolynomialConverter::convertConstraint` path
  `assertInterfaceEquality` already feeds `engine_` (`cc.diff rel 0`), with its
  reason lit appended to `activeReasons` (index ⇒ reason). A shared term that is
  not NRA-poly-expressible ⇒ DEFER the whole CAC run to Collins (sound floor).
- **UNSAT** ⇒ a gap-free covering of (NRA ∧ interface (dis)eqs) is a combination
  conflict. The conflict clause is drawn from `CacResult::unsatCore` (per-cell
  origins, `XOLVER_NRA_CAC_MIN_CONFLICT`) or the full `activeReasons` — EITHER
  way it includes the interface lits that participated, so the SAT core cannot
  relearn the arrangement. Still gated behind `XOLVER_NRA_CAC_TRUST_UNSAT`.
- **SAT** ⇒ v1 DEFERS to Collins (engine_ has the interface constraints): the
  N-O arrangement read-back (shared-term values) is NOT yet exposed — that is
  the remaining EQNA-paired step (#43 below). Sound: Collins is the validated
  SAT+arrangement baseline.

REMAINING (EQNA-paired): (a) expose shared-term values in the CAC SAT model so
the arrangement can be read back (then stop deferring SAT); (b) coordinate the
effort-schedule + deadline; (c) flip the gate after the UFNRA differential.
The seam EQNA owns is the stageCac gate + conflict consumption — do NOT dual-edit.

## Task #43 — SAT arrangement read-back (design contract, queued for EQNA-pairing)

STATUS: design pinned, NOT built. WAIT for EQNA's Track 3 mechanism (UF model
extraction / functionInterps surfaced via `TheoryManager::getModel`) to land —
do NOT pre-empt their getModel shape. When their channel is exposed, plug in.

WHAT THIS CLOSES. The combination-aware CAC (`XOLVER_NRA_CAC_COMBINATION`)
currently DEFERS SAT to Collins because the N-O arrangement needs every shared
term's value (rational or algebraic) — the SAT model already assigns the NRA
vars, but the combination loop reads back shared-term values from the theory
model to build the arrangement. Once EQNA's read-back channel is live, CAC SAT
under combination can return its own model directly (rather than deferring),
unlocking the standalone NRA SAT wins (+5 in the headline diff) for QF_UFNRA.

WHAT I NEED FROM EQNA (read-only contract; do NOT pre-empt the shape):
1. The CHANNEL EQNA's combination loop uses to read a shared term's value out
   of an arith theory's getModel — most likely a typed-channel entry keyed by
   the shared term's name (the same name the converter resolved when the
   interface (dis)eq was asserted). Document the channel name + value type
   (mpq_class for rationals, plus whatever the algebraic encoding is).
2. Whether algebraic values are accepted on that channel today, or whether
   only rationals round-trip. If algebraic isn't accepted yet, my SAT path
   stays DEFER for the algebraic case (still sound).
3. The cb_propagate sequencing — when the combination loop actually CONSULTS
   the read-back (so I know when the model must be populated).

MY SIDE (build when EQNA's channel is up — single seam touch):
1. `NraSolver::getModel()` already returns the SAT sample as `satFastModel_`
   (rational vars). Under combination, ADD a pass that resolves every shared
   term in `sharedTermRegistry_` to a polynomial via `converter_`, evaluates
   that polynomial at the SAT sample (the CAC `satModel_`), and emits the
   result on EQNA's channel.
   * Evaluation at a RATIONAL sample is exact polynomial arithmetic →
     definite rational value, channel-ready.
   * Evaluation at an ALGEBRAIC sample yields an algebraic value (built via
     the existing `RealAlg` machinery). Emit IFF EQNA's channel accepts
     algebraic; else keep deferring (the existing v1 SAT-defer).
2. `stageCac` SAT branch: when `cacCombination` + interface set non-empty +
   shared-term emission succeeded for every entry → return `consistent()` +
   stash `satFastModel_`. Else keep the current `return std::nullopt` → Collins.
3. Validate: the same SAT model that `allHold` certified against
   `presolveConstraints_` (incl. lifted interface constraints) must ALSO
   satisfy every shared-term equality the combination loop sees — the lifted
   `poly(a)-poly(b) = 0` constraint is exactly what makes the shared values
   equal under the model, so this is automatic. Belt-and-suspenders: assert
   `value(a) == value(b)` on the emission channel for each interface eq.

GATE (when built): QF_UFNRA differential vs z3 — the standalone +5 SAT wins
from the headline diff must now fire under combination. QF_NRA reg stays
inert (the new SAT-emission path runs only when `cacCombination` + interface
set non-empty). 0 unsound in reg+differential.

SEAM DISCIPLINE: edits ONLY in `NraSolver::getModel` + the SAT branch of
`stageCac`. No edits to `cb_propagate` / `SharedEqualityManager` / EQNA's
getModel mechanism. Coordinate the channel-name pin with master before building.

## Combination-aware CAC (UFNRA medal lane) — ORIGINAL DESIGN SCOPE (pair with EQNA)

PROBLEM. Today the fast NRA stages (sign-refute, subtropical, CAC) DEFER (return
nullopt) whenever interfaceEqualities_/interfaceDisequalities_ is non-empty, so in
UFNRA the +volume CAC wins never apply — the base CDCAC handles the shared
constraints. To score the medal lane, CAC must run UNDER the N-O interface
constraints, not defer. This scopes the mechanism; the build is EQNA-paired
(touches the combination loop EQNA owns — do NOT dual-edit that seam).

MECHANISM (interface constraints → CAC constraints; root-/sign-preserving):
1. Interface EQUALITY (shared a = shared b): add the constraint poly(a)-poly(b) = 0
   to the CAC constraint set (Relation::Eq). A real algebraic constraint — CAC
   treats it like any equality.
2. Interface DISEQUALITY (a != b): add poly(a)-poly(b) != 0 (Relation::Neq). CAC's
   covering must exclude cells where the diff vanishes; Neq is already in the
   relation set. Both are sound: they are genuine constraints over the NRA vars.
3. The shared terms must be NRA-polynomial-expressible (via sharedTermRegistry_ +
   PolynomialConverter). If a shared term is not poly-expressible (e.g. a UF app
   feeding a real var) → CAC must DEFER for that constraint (sound floor), exactly
   as the purifier boundary requires.

CELL CERTIFICATES UNDER COMBINATION (soundness generalizes directly):
- A cell is truth-invariant for ALL constraints incl. the interface polys — the
  same per-constraint sign-invariance argument; the interface (dis)eq polys are
  just more delineators in the characterization. No new cert machinery: the
  square-free reduction + the unsatTrustworthy_ ledger carry over unchanged.
- SAT: the CAC model must assign every SHARED term a definite value (rational or
  algebraic) so the combination layer can read the arrangement back. satModel_
  already assigns the vars; expose the shared-term values (algebraic ok — the N-O
  exchange compares them via compareRealAlg, now certified).
- UNSAT: a gap-free covering of (NRA constraints ∧ interface (dis)eqs) is a
  COMBINATION CONFLICT. The conflict clause MUST include the interface (dis)eq
  REASONS (the SatLits the combination layer attached), not just the NRA
  constraint reasons — else the SAT core relearns the same arrangement. CAC already
  tracks activeReasons per constraint; extend to carry the interface-(dis)eq lits.

INCREMENTALITY:
- v1 (sound, simple): one-shot CAC re-run with the CURRENT interface set; re-run
  when the set changes. Correct, just not incremental. Ship this first.
- v2 (later): incremental covering reuse across interface-set deltas. Not now.

SEAM / OWNERSHIP (the non-negotiable coordination point):
- CAC's contract to the combination layer: consume interfaceEqualities_/
  interfaceDisequalities_ (already populated via addInterfaceEquality) as extra
  constraints; return SAT(model incl. shared-term values) / UNSAT(conflict whose
  clause includes the interface-(dis)eq lits) / Unknown.
- EQNA owns TheoryManager + SharedEqualityManager (the loop that populates the
  interface set and consumes the conflict). The ONLY shared edit is the stageCac
  gate (stop deferring on non-empty interface set) + the conflict-clause assembly.
  Pair on: (a) the exact reason-lit plumbing for the conflict, (b) shared-term
  value read-back for the arrangement, (c) when CAC is invoked in the combination
  effort schedule (likely Full-effort, mirroring QF_NRA, with the same wall-clock
  deadline yielding to the base CDCAC).
GATE for the eventual build: combination reg (UFNRA) OFF+ON 0-unsound + the
QF_NRA reg stays 143/143 (the gate change must be inert when no interface set).
