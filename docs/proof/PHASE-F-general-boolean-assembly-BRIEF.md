# Phase F — General Boolean Assembly (LRAT → Alethe): clean-context implementation brief

Status: **design + de-risking done, not yet implemented.** This is the brief for a
fresh-context agent to execute, in the same style as the (completed) euf_003
bool-congruence increment. Read `MEMORY → proof-implementation-state.md` (#15 section)
for the broader context first.

## What this closes

Today, theory instances that need a **multi-conflict** refutation are
`VERIFIED-SKELETON (N lemmas assumed)`: the Boolean core is a DRAT proof
(`drat-trim`-verified) over a CNF that includes the theory lemmas **as input
clauses**, but those lemmas are *assumed*, not proven, and the whole thing is a
separate DRAT artifact rather than one Carcara-checkable Alethe proof. The single
theory conflict that refutes a set of top-level literals is already handled (LRA/IDL/
RDL la_generic + EUF transitivity/congruence/refl/bool-congruence — 74 VERIFIED,
0 REJECTED). The general case (`euf_016/039/061`, combination) is the remaining gap.

The goal: emit **one Alethe proof, Carcara-verified against the original SMT problem**,
that (a) clausifies the asserted formulas, (b) replays the SAT resolution refutation,
and (c) discharges each theory lemma with its own theory sub-proof.

## The three parts (and why it is a subsystem, not an increment)

1. **Clausification / Tseitin proof** (formula → CNF clauses, in Alethe). Carcara
   checks the proof against the *formula* (the `.smt2` assertions), but resolution
   runs over *clauses*. Each asserted formula must be turned into `(cl ...)` clauses
   via Alethe clausification rules before resolution. For a Tseitin CNF with shared
   subterms this is a tree of `and`/`or`/`implies`/`ite`/`not` rules plus Tseitin
   *definition* clauses for the proxy variables. **This is the hardest sub-part** and
   the real reason this is a subsystem.
2. **LRAT → Alethe resolution.** CaDiCaL can emit LRAT (it has internal LRAT support;
   `third_party/cadical/src/*` has `LRAT_ID`/`lrat_chain`). Each LRAT line is a clause
   derived by resolution with **explicit antecedent clause-ids** — translate each to an
   Alethe `(step ti (cl ...) :rule resolution :premises (...))`. Mechanical once you
   have LRAT + a clause-id → Alethe-step-id map. (DRAT alone is NOT enough — it has no
   antecedents; you need LRAT's hints.)
3. **Per-lemma theory sub-proofs.** Each external (theory) clause used by the LRAT
   refutation must be *derived* (not assumed) by its theory justification — exactly the
   `(cl ¬l1 .. ¬lk)` tautology the existing single-conflict machinery already builds
   (`buildConflictRefutation`, `EufCongruenceProver`, the la_generic verifier). Splice
   each lemma's sub-proof in where the LRAT refutation cites that clause.

## De-risked Alethe shapes (ALL validated against Carcara — trust these)

Scratchpad `/tmp/tseitin`, `/tmp/boolcong`, `/tmp/nary`:
- `or` clausifies a disjunction: premise `(or a b)` → `(step t (cl a b) :rule or :premises (h))`. **valid.**
- `and` extracts a conjunct: premise `(and x y)` → `(step t (cl x) :rule and :premises (h) :args (0))`. **valid** (REQUIRES `:args(index)`).
- `resolution` over `(cl ...)` clauses: order-insensitive, **equality-orientation-sensitive**, implicit-pivot n-ary. **valid.**
- Theory tautology clauses: `eq_congruent`, `eq_transitive`, `la_generic :args (coeffs)`, `equiv1`/`equiv2`, `refl` — all valid (used by the merged single-conflict increments).

Minimal end-to-end already shown valid: `(assert (or a b))(assert (not a))(assert (not b))`:
```
(assume h1 (or a b)) (assume h2 (not a)) (assume h3 (not b))
(step t1 (cl a b) :rule or :premises (h1))
(step t2 (cl) :rule resolution :premises (t1 h2 h3))
```

## Recommended STAGING (do not attempt all three parts at once)

**Increment F1 — pure-propositional unsat as a single Alethe proof (NO theory lemmas).**
Target the `tests/regression/bool/` lane cases currently verified by DRAT only (e.g.
small pigeonhole / clausal unsats). These have *no* theory lemmas, so part 3 is empty —
F1 isolates parts 1 (clausification) + 2 (LRAT→Alethe) end-to-end. This is the right
first end-to-end proof. Gate: ≥1 bool-lane case flips from DRAT-only to
`VERIFIED (alethe/carcara)`, 0 REJECTED, corpus VERIFIED(complete) rises.

**Increment F2 — add theory-lemma sub-proofs (part 3).** Once F1 replays a Boolean
refutation in Alethe, splice each external/theory clause's tautology sub-proof. Gate:
`euf_016`/`euf_039` (and ideally `euf_061`) flip from SKELETON to VERIFIED, 0 REJECTED.

## Blockers / investigation pointers

- **B1 — emit LRAT, not just DRAT.** `src/sat/CadicalBackend.{h,cpp}`: `ProofCnfCapture`
  (a `CaDiCaL::Tracer`) currently records all clauses flat via `add_original_clause`
  and a separate file trace writes DRAT. You need LRAT: either CaDiCaL's `FileTracer`
  in LRAT mode or a custom `Tracer` capturing `add_derived_clause` WITH the antecedent
  chain (the LRAT hints). Confirm CaDiCaL exposes the antecedents through the Tracer API
  (`add_derived_clause(id, redundant, clause, antecedents)`-style). Wire it behind
  `XOLVER_ENABLE_PROOFS` + `--produce-proof`.
- **B2 — clause-id → meaning map.** You must map each CNF clause id to either (a) an
  asserted formula's clausification, or (b) a theory lemma (with its theory cert).
  `ProofCnfCapture` distinguishes original vs external by *insertion order* (the
  `assumed` count = captured − original `addClause` count). You need a richer record:
  per external clause, capture the theory justification. The theory side already pushes
  conflicts to `proof::TheoryProofSink` (see `src/api/Solver.cpp` `proofSink_`); extend
  it / cross-reference so EVERY theory lemma clause fed to CaDiCaL has a retrievable
  cert (rule + lits + args). PROPAGATION/instantiation lemmas may not currently be in
  the sink — audit `CadicalTheoryPropagator` clause-feed points.
- **B3 — var ↔ atom map for clausification.** The Atomizer (`src/frontend/atomization/`)
  owns `b_i ↔ theory atom_i`. To clausify a formula in Alethe you need, per CNF
  variable, the IR atom it stands for (rendered via `dumpExprToSMT2`). Recover this map
  from the Atomizer (it already exists for model output / the single-conflict atoms).
- **B4 — Tseitin definition proofs.** Shared subterms get proxy vars `p ↔ subformula`.
  Their defining clauses need Alethe `and_pos`/`or_pos`/… or the connective-specific
  rules. Start F1 on cases with NO shared subterms (flat clausal) to defer B4; widen
  later. (The n-ary/boolpur EUF cases DO have proxies — they are F2+B4 territory.)

## Verification gates (ALL must pass before committing — same as every proof increment)

1. The targeted case → Carcara `valid` (`carcara check <base>.alethe <base>.smt2`).
2. Full proof corpus **0 REJECTED**, VERIFIED(complete) **rises** (currently 74):
   `grep -rl ':status unsat' tests/regression/{bool,lra,euf,idl,rdl} | sort > /tmp/c.txt && bash tools/proof/run_proof_corpus.sh build/bin/xolver "$PWD/.proof-checkers/drat-trim/drat-trim" /tmp/c.txt "$PWD/.proof-checkers/carcara/bin/carcara"` → `REJECTED=0`, exit 0.
3. Unit `./build/tests/xolver_unit_tests` → SUCCESS (currently 1493).
4. Regression `python3 tools/regression/run_regression.py --root tests/regression --solver build/bin/xolver` → **0 UNSOUND, 0 UNEXPECTED_FAIL** (a lone `nra_200` TIMEOUT is a known flake).
5. `bash tools/governance/check_architecture.sh` → satisfied.
6. **Behaviour-neutral**: all new code `#ifdef XOLVER_ENABLE_PROOFS`; competition (proofs-OFF) build byte-identical. The DRAT path must remain available as the fallback when an Alethe assembly can't be produced (degrade, never a wrong proof).

## Workspace / build / workflow

Worktree `/mnt/d/D_Work/ISCAS/projects/xolver-proof`, branch `proof/implementation`.
Build: `ulimit -v 4194304 && cmake --build build -j2` (keep `-j2`; WSL). Checkers under
`./.proof-checkers/`. Produce a proof: `XOLVER_ENABLE_PROOFS=1 ./build/bin/xolver solve
<f>.smt2 --produce-proof <base>` → `<base>.alethe` + `<base>.smt2` (and `.cnf`/`.drat`).
Commit only if ALL gates pass; `git push` to `proof/implementation` (do NOT merge to
main — that is the human's `git push origin proof/implementation:main` ff step after CI
`proof-gate` is green). If blocked, report the precise obstacle and stop — no half-done
code.
