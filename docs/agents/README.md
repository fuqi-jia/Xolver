# SOTA Solving Campaign — 5-Agent Charters

**Goal:** push Zolver toward SOTA solving power across the **full per-theory solving
stack** — not just preprocessing. The technique menus and recommended minimal
"超越集" (minimal set to beat SOTA) live in `conversations/5.list/*.md`, one file per
theory. Those files are each agent's **authoritative bible**.

This is **not** a one-shot task list. Each brief is a **charter** for an area: the agent
audits what already exists, then fills the highest-leverage gaps from its theory's minimal
set, one flag-gated+validated technique at a time. The master (coordinating session) feeds
Phase-2 targeted tasks from the panda1/panda7 benchmark discrepancies.

Each brief is meant for a **fresh, separate Claude Code instance** launched in the repo
root (`/mnt/d/D_Study/BUAA/projects/NLColver`). Each works in its **own git worktree** and
does **not** merge to `main` — the master integrates the branches.

## The partition (3 theory-pairs + 2 cross-cutting)

| Agent | Bible | Branch | Owns | Area |
|---|---|---|---|---|
| [A1](agent-1-linear.md) | `1.chatgpt.lra.md`, `2.chatgpt.lia.md` | `agent/a1-linear` | `theory/arith/{lra,lia,idl,rdl,linear,integer}` | Linear arithmetic full stack |
| [A2](agent-2-nonlinear.md) | `3.chatgpt.nra.md`, `4.chatgpt.nia.md` | `agent/a2-nonlinear` | `theory/arith/{nra,nia,nira,lira,icp,interval,linearizer,bit_blast,poly,search}` | Nonlinear arithmetic full stack |
| [A3](agent-3-uf-arrays.md) | `5.chatgpt.uf.md`, `6.chatgpt.ax.md` | `agent/a3-uf-arrays` | `theory/{euf,array}` | EUF + Arrays full stack |
| [A4](agent-4-combination-cdclt.md) | cross-cutting §§ of all 6 | `agent/a4-combination-cdclt` | `theory/combination`, `theory/core/{TheoryManager,TheoryLemmaDatabase}`, `sat/` | Theory combination + CDCL(T) integration |
| [A5](agent-5-strategy-preprocessing-infra.md) | portfolio/preproc/cache/model §§ of all 6 | `agent/a5-strategy-infra` | `frontend/{factory,preprocess,atomization}`, `expr/rewriter`, `api/Solver`, `util/` | Strategy/portfolio + rewriter/preprocessing + shared infra |

## The method every agent follows

1. **Read your bible** (the conversation file[s]) — especially the **最小超越集 /
   minimal set** it recommends and the "最不能省 / must-do" groupings.
2. **Audit the codebase** against that minimal set: for each item, mark
   EXISTS-and-good / EXISTS-but-weak / MISSING, with file:line evidence. Zolver is mature
   (it has simplex, CDCAC, an e-graph, a presolve fixpoint, bit-blast) — **do not
   re-implement what exists**; improve the weak and add the missing.
3. **Prioritize by leverage** (the bible flags which items are decisive vs. nice-to-have).
4. **Implement top items**, each behind a default-OFF flag, each validated. Iterate.
5. **Report** your gap-analysis table + what you implemented + measured effect.

## Common contract (every agent)

1. **Soundness is absolute.** Every change preserves the solver's verdicts. `ModelValidator`
   re-checks SAT models against the *original* assertions, so a bad SAT model is caught —
   but **nothing catches unsound UNSAT / wrong propagation**. A bad conflict, a dropped
   model, a wrong cut, a missing extensionality lemma → silent unsoundness. Prove each
   technique preserves soundness; for SAT keep the validation path intact.
2. **Default-OFF env-var flag** per technique, read once via `std::getenv`. Naming:
   `ZOLVER_<AREA>_<TECH>` (e.g. `ZOLVER_LRA_DUAL_SIMPLEX`, `ZOLVER_NIA_LOCALSEARCH`,
   `ZOLVER_AX_WEAKEQ`, `ZOLVER_COMB_CAREGRAPH`, `ZOLVER_STRAT_PORTFOLIO`). The benchmark
   binary is static; env flags let one binary A/B test without rebuild.
3. **Double validation gate** before any task is "done":
   - flag **OFF**: unit (`zolver_unit_tests`, ~702) + regression (632) green, 0 unsound
     (no regression to the default path).
   - flag **ON**: same suites green, 0 unsound (new path correct). Pay special attention
     to your theory's regression bucket (see counts below).
4. **Add tests:** unit tests for new components + SMT2 regression cases under
   `tests/regression/<logic>/`.
5. **Stay in your directories. Don't merge to main.** If you must edit a shared file
   (`api/Solver.cpp`, `PresolveEngine.cpp`, `TheoryFactory.cpp`, `TheoryManager`), keep it
   minimal/additive and call it out in your report — the master merges.
6. **Consult, don't copy:** `reference/z3/` and `reference/cvc5/` are in-tree for reading.
   Do not copy code (licensing unsettled).

Regression bucket sizes (for your flag-ON focus): lra 57, lia 52, idl 15, rdl 12, nra 139,
nia 109, nira 30, lira 37, euf 62, ax 10, alia 9, alra 6, auflia 5, auflra 3, uflia 25,
uflra 10, ufnia 10, ufnra 7, bool 31.

## Promotion policy — soundness floor vs answer recovery (read this)

Two layers, don't confuse them:

- **FLOOR** (A5's `ZOLVER_PP_STRICT_VALIDATION`, A2's NRA UNSAT-cert gate, and the combination
  UNSAT floor still owed by A4): never emit an answer we can't confirm. A `sat` we can't validate
  → `unknown`; an `UNSAT` we can't certify → `unknown`. This is the soundness **guarantee** and
  defense-in-depth — latent bugs exist (e.g. A3's mid-saturation `explainEquality` false-UNSAT,
  only reachable once the solver got fast enough). A validator/checker can only ever produce
  *correct-or-`unknown`*; it cannot turn a wrong model into the right answer.
- **RECOVERY** (every theory agent): `unknown` → **CORRECT answer**. This is the real work and the
  only thing that scores. Fix model extraction / reasoning so the solver produces a correct,
  *validatable* model (validator confirms → correct `sat`) or correctly proves `unsat`.

**The destination of every false-SAT / false-UNSAT is a CORRECT answer, never `unknown`.** `unknown`
is the safety net we stand on so we're never *wrong* while recovery lands — it is never the goal.

Scoring reality: **correct > unknown > wrong.** A wrong answer is disqualifying in SMT-COMP; `unknown`
just scores 0. So a gate that turns wrong→unknown is a strict improvement — but stopping there trades
wrong answers for zeros, which is why RECOVERY is mandatory, not optional.

**END-STATE INTENT: every capability is meant to be default-ON.** These flags are efficiency
improvements; default-OFF is a *temporary* safety state while correctness (and efficiency) are
unverified, NOT the destination. A flag is never "discarded" for being imperfect — it's "not yet
finished." The job is to verify each one and flip it on.

**HARD PROMOTION GATE (master-enforced at integration) — a flag flips to default-ON when BOTH hold:**
1. **Sound** — 0 wrong answers, and its `unknown`-flips driven down to only the genuinely-hard
   residual (we won't ship a solver that returns `unknown` *more* than the current default); AND
2. **Actually delivers its efficiency** — net solve-count / speed GAIN on a panda A/B, not a
   regression. Sound-but-slower is "not finished," not "ready": e.g. `ZOLVER_LIA_CUTS` is sound
   (0 mismatch) but currently *regresses* LIA to 47.5% timeout, so it stays OFF until cut-management
   makes it net-positive — then it goes on.

So OFF is temporary for every flag; the destination is all-on. See `docs/strict-validation-flips.md`
for the strict-validation flips bucketed by owning agent (each an "`unknown` → correct" task), and
each round's panda A/B for the efficiency half.

**RE-VALIDATION RULE:** any speedup/completeness gain must be re-checked differentially vs z3 on the
cases it *newly makes reachable* — timeouts mask latent soundness bugs, so a prior "0 unsound" does
not transfer to the faster build.

## Worktree setup (every agent runs first)

```bash
cd /mnt/d/D_Study/BUAA/projects/NLColver
git worktree add -b <your-branch> ../zolver-<your-id> main
cd ../zolver-<your-id>
git submodule update --init --recursive
mkdir -p build && cd build && cmake .. && cmake --build . -j 2   # -j 2: WSL OOMs on -j
```

Validation commands (from worktree root):

```bash
cd build && cmake --build . -j 2 && cd ..
./build/tests/zolver_unit_tests
./build/tests/zolver_unit_tests --test-case="<name>"
python3 tools/run_regression.py --root tests/regression --solver build/bin/zolver --timeout 20 -j 2
```

## Reporting format (every agent)

```
## Result — Agent <N> (<area>)
Branch: <branch>
Gap-analysis: table of bible-item → EXISTS-good / EXISTS-weak / MISSING (file:line)
Implemented this round: <technique> (flag ZOLVER_*), <technique> (flag ...)
Files touched: <list>  (shared-file edits listed separately)
Validation: unit OFF/ON, regression OFF/ON (PASS counts), unsound count
New tests: <list>
Local measured effect: <before/after on a sample, if measurable>
Backlog (next-highest-leverage items left): <ordered list>
Open questions / risks for master: <...>
```

## Phases

- **Phase 1 (now):** all five audit + implement against their bibles' minimal sets.
- **Phase 2 (when panda1/panda7 land):** master triages discrepancies (soundness first),
  attributes each to a subsystem, feeds targeted fix-tasks to the owning agent.
  Benchmark-proven flags get promoted to default-on.

## Master integration checklist (coordinating session)

1. Per branch: checkout, build, run flag-ON + flag-OFF suites.
2. Merge branches one at a time into an integration branch; re-run combined suites.
3. Resolve known shared-file overlaps: `Solver.cpp` (A5), `TheoryManager`/`sat` (A4 + theory
   agents' explanation interfaces), `PresolveEngine.cpp` (A1/A2), `TheoryFactory.cpp` (A5).
4. A/B each promoted flag on the benchmark before defaulting it on.
