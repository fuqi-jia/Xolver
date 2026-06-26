# Proof-format & checker reference index (Phase A)

Curated, version-pinned references for the unsat-proof pipeline. The decision
and per-theory mapping that *use* these live in `../RESEARCH.md`. Large specs are
vendored alongside this file so the branch is self-contained; checker tools are
code repos, pinned here by version rather than vendored.

> **Provenance rule (CLAUDE.md):** these are *published formats and algorithms*.
> No z3/cvc5 source or symbol names are copied. cvc5/veriT are cited only as
> reference *producers* of the open Alethe format, never as a code source.

---

## 1. Target proof format — Alethe

- **Spec:** *The Alethe Proof Format: An Evolving Specification and Reference*
  (Barbosa, Reynolds, Schurr, et al.). Vendored: **`alethe-spec.pdf`**.
  Canonical URL: <https://verit.loria.fr/documentation/alethe-spec.pdf>
- **What it is:** an SMT-LIB-based proof format with both coarse- and
  fine-grained steps; clauses are written with the `cl` operator; proofs are a
  list of `assume` / `step` commands with `anchor`-delimited subproofs. ~90 rules.
- **Why it fits Xolver:** built on SMT-LIB (Xolver already parses/prints it);
  has first-class rules for exactly Xolver's theories — `la_generic` (linear
  arithmetic Farkas combination, **takes rational coefficients as arguments**),
  `eq_congruent`/`eq_transitive` (EUF), resolution for the SAT core; and a
  `hole` rule for steps a checker need not verify (degraded escape hatch).
- **Key rules for our theories** (names; full mapping in `../RESEARCH.md`):
  - SAT core: `resolution`, `th_resolution`, `contraction`, `tautology`,
    `reordering`.
  - Clausification/Tseitin: `and`, `or`, `not`, `implies`, `and_pos`, `and_neg`,
    `or_pos`, `or_neg`, `implies_pos`, `implies_neg`.
  - EUF: `eq_reflexive`, `eq_transitive`, `eq_congruent`, `eq_congruent_pred`;
    subproof rules `refl`, `trans`, `cong`, `symm`.
  - LRA/LIA: `la_generic` (Farkas), `la_disequality`, `la_totality`,
    `la_tautology`, `la_rw_eq`, `la_mult_pos`, `la_mult_neg`, `lia_generic`.

## 2. Alethe checker — Carcara

- **Repo:** <https://github.com/ufmg-smite/carcara> (TACAS 2023). Pinned version
  **1.1.0** (latest tagged release 2023-08-29); we will pin the exact commit in
  CI in Phase E.
- **Paper:** *Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs
  in the Alethe Format*, TACAS 2023.
  <https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19>
- **Install:** `cargo install --git https://github.com/ufmg-smite/carcara.git`
  (needs Rust/Cargo **1.87+**). Or `cargo build --release && cargo install --path cli`.
- **Check a proof:** `carcara check example.smt2.alethe example.smt2`
  (proof file first, original SMT-LIB problem second). `carcara elaborate …`
  expands coarse steps into fine ones.
- **Role:** the independent external checker — the unsat-side analogue of
  Xolver's `ArithModelValidator`. A proof Xolver emits is only "verified" when
  Carcara (a separate tool, separate authors) accepts it. **90 rule checkers.**
- Useful flags to evaluate in Phase D: `--allow-int-real-subtyping`,
  `--expand-let-bindings`, strict mode (confirm against the installed `--help`).

## 3. Propositional core — DRAT / LRAT

The Boolean refutation is emitted by the vendored CaDiCaL (**rel-3.0.0**, which
ships a native `LratTracer` — see `../RESEARCH.md` §CaDiCaL). It is checked by an
independent SAT-proof checker:

- **DRAT-trim / lrat-check:** <https://github.com/marijnheule/drat-trim>
  (papers vendored: `drat-trim.pdf`, `lrat-efficient-certified-rat.pdf`).
  - Build: `make`.
  - Check DRAT: `drat-trim <cnf.dimacs> <proof.drat>` — **the gate.** Full forward
    RUP; **adversarially sound** (rejects a bogus empty-clause proof of a SAT
    formula). Exit 0 + `s VERIFIED` = accepted; exit 1 + `s NOT VERIFIED` = reject.
  - Emit LRAT from DRAT: `drat-trim <cnf> <proof.drat> -L <proof.lrat>`.
  - Check LRAT: `lrat-check <cnf.dimacs> <proof.lrat>` (the in-repo C checker).
    **CAVEAT — verified Phase A:** this `lrat-check` *trusts* solver-supplied
    antecedent hints and rubber-stamps an empty clause when the hints don't
    independently conflict; it is **fine for genuine solver output but NOT a gate
    against a wrong proof.** Do not use it as the sole soundness gate. See
    `checker-soundness-test.sh` for the reproducible adversarial test.
- **LRAT format:** *Efficient Certified RAT Verification* (Heule, Hunt, Kaufmann,
  Wetzler), CADE 2017 — vendored `lrat-efficient-certified-rat.pdf`. LRAT extends
  DRAT with antecedent **hints** so a checker needs no unit propagation search;
  this is what makes formally-verified checking (cake_lpr) cheap.
- **DRAT format:** *The DRAT Format and DRAT-trim Checker* (Wetzler, Heule, Hunt)
  — vendored `drat-trim.pdf`.
- **Verified LRAT checkers (Phase E hardening option):**
  - `cake_lpr` — CakeML-verified LRAT checker (machine-checked soundness).
  - CaDiCaL ships an internal `LratChecker` (`third_party/cadical/src/lratchecker.hpp`).

## 4. Alternative format — LFSC (kept as fallback, not chosen)

- **What:** Logical Framework with Side Conditions; proof terms checked by the
  `lfscc` checker. The scaffold already names `exportLFSC()`.
- **Why not default:** the LFSC checker + signatures are heavier to integrate
  than push-button Carcara; the Alethe ecosystem (Carcara, Rust, maintained,
  push-button, SMT-LIB-native) is the lower-friction soundness gate for our
  theories. LFSC remains a documented fallback if an Alethe rule proves
  intractable for a given theory.

## 5. Theory-certificate literature (algorithms only)

Published algorithms behind each theory's checkable certificate. Used as
*algorithmic attribution*; no solver source is copied.

- **Farkas / Simplex infeasibility certificate:** Farkas' lemma — a nonneg.
  rational combination of the asserted (in)equalities yielding `0 < 0` / `0 ≤ -1`.
  This is precisely the argument vector of Alethe `la_generic`. (Dutertre–de Moura
  simplex-for-SMT is the standard algorithmic reference for extracting the
  multipliers from a final infeasible simplex tableau.)
- **EUF congruence-closure proofs:** Nieuwenhuis & Oliveras, *Proof-Producing
  Congruence Closure* (RTA 2005) — the proof-forest / explain(·) mechanism.
  Xolver's `src/theory/euf/ProofForest.*` already implements this.
- **Integer cuts / branches:** Gomory cut and branch-and-bound refutations;
  Cooper/Omega elimination certificates. Alethe `lia_generic` is the (holey)
  catch-all; tight integer steps need explicit cut justification.
- **Difference logic:** a negative-cycle in the constraint graph (Bellman–Ford)
  is itself the Farkas certificate (sum the cycle's edge constraints → `0 < 0`).
- **NRA / nonlinear:** Collins CAD, Lazard/McCallum projection, NLSAT/CDCAC cell
  certificates; positivstellensatz/`nlsat`-style sign-condition certificates.
  These are research-hard to render as checkable Alethe; see the gap analysis in
  `../RESEARCH.md` — gated to degraded "no-proof" mode initially.

---

## Pinned versions (snapshot for reproducibility)

| Component | Version / commit |
|-----------|------------------|
| Vendored CaDiCaL | `rel-3.0.0` (`7b99c07`) — native DRAT + LRAT tracers |
| Carcara | 1.1.0 (commit to be pinned in CI, Phase E) |
| drat-trim / lrat-check | `marijnheule/drat-trim` HEAD (pin in CI) |
| Alethe spec | vendored `alethe-spec.pdf` |
