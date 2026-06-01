# Long-Async-Dispatch Pattern (Master-Absent Agent Self-Organisation)

**Author**: NRA-lane agent (Task Z, 2026-06-02).
**Source**: distilled from 49 commits across the post-compact Tasks
I/J/K/L → M/N → Q/R/S/T/U → V/W/X/Y/Z chains, executed without master
intervention on `agent/nra-2`.

When master dispatches a 5-task queue with the expectation that "your
queue should be empty by the time master returns 8 h later", this is
the pattern that **shipped** while preserving the soundness gate. Other
lanes can use it whenever they receive similar long-async-dispatch
instructions.

---

## The rule

> Each dispatch from master contains 4-6 priority-ordered tasks of
> **decreasing risk** and **decreasing leverage**. The agent walks the
> queue top-to-bottom. **Negative findings count as closure** — a task
> rejecting its candidate via the 4-step audit methodology is **DONE**,
> not "stalled". Stalling is wasted time when master returns.

The pattern's bet: master cannot keep five tasks blocked behind one
unresolvable item. By making "deferred with documented reason" a
first-class closure state, the queue drains every cycle.

---

## When NOT to use this pattern

| Anti-pattern | Why |
|---|---|
| Tasks have hard ordering dependencies | The pattern assumes you can drain in any order; if Task B truly cannot start before Task A ships, this is a sequential plan, not a queue. |
| You're blocked on master's decision | Don't fake-close — if a task says "master GREEN-LIT" and master hasn't, the right move is *escalate the block*, not ship. |
| Tasks touch user-facing safety surfaces | Soundness gates require slower verification; don't compress 4-step audits into 30 min if the consequence of a wrong "ship" is a false-UNSAT. |
| You're in plan mode | Dispatch is for execution, not planning. Switch out of plan mode first. |

---

## The 5-task queue design

A well-formed dispatch from master has this shape (from the observed
Q-U and V-Z queues this session):

```
Priority 1 (★★★)  HIGH-LEVERAGE, HIGH-RISK
  - Ship-level change, source-flip, default-promotion
  - 2-3 h budget, requires paired test, must keep audit trail
  - Example: Task Q (LOCALSEARCH + CAC_SR_CACHE source promotion)
  - Example: Task V (cross-lane direct application to EUF)

Priority 2 (★★)   MEDIUM-LEVERAGE, MEDIUM-RISK
  - Continued audit / sample expansion / new candidate ship
  - 1-2 h budget, single layer/component, paired test if shipping
  - Example: Task R (LibPolyKernel cousin audit continued)
  - Example: Task W (cross-lane apply to DT validator)

Priority 3 (★★)   MEASUREMENT / PREDICTION
  - Profile, gather evidence, calibrate against future ground truth
  - 1-2 h budget, no soundness risk (read-only)
  - Example: Task S (AlgebraicNumber layer audit, no ship surface)
  - Example: Task X (local pre-validate hash-cons stack)

Priority 4 (★)    INFRASTRUCTURE / SHIP-PREP
  - Documentation, reg suite expansion, flag matrix
  - 1-2 h budget, very low risk
  - Example: Task T (SparseTableau cross-lane, defer doc only)
  - Example: Task Y (Stage 5 ship-prep flag matrix)

Priority 5 (★)    META / DOCUMENTATION
  - Pattern docs, lessons-learned, cross-lane export
  - 1 h budget, zero risk
  - Example: Task U (NRA reg expansion with stress cases)
  - Example: Task Z (this document)
```

The decreasing risk lets the agent fall back: if Priority 1 needs an
unexpected revert mid-task, Priorities 2-5 are unblocked and remain
shippable.

---

## The four-step execution rule

For each task in the queue:

### Step 1 — Read the spec literally

The master's task description is the contract. If it says "if hit rate
< 50 %, skip", that's the ship gate, not a "try harder" suggestion. The
spec is the truth.

### Step 2 — Execute the smallest verifying experiment

If the task is "audit X", the minimum verifying experiment is **count
the calls** (instrument without caching) before assuming X is hot. If
the task is "ship Y", the minimum verification is **run the lane's reg
suite before AND after**, with the pre-binary stashed.

Pre-binary stashing is **essential** — every ship task this session
kept `/tmp/nra_task_i/xolver_pre_Q.bin` for paired comparison. Without
the pre-binary, "did this change break X" is unanswerable.

### Step 3 — Decide ship vs revert vs defer

Three closure states:

* **Ship**: hit rate clears threshold, paired reg PASS, soundness gate
  green. Commit, push, update task to completed.
* **Revert**: change is functionally a no-op (e.g. instrumentation
  added 0 / 0 calls). Restore the original code, commit the revert with
  the empirical evidence, update task to completed.
* **Defer**: structural finding that's NOT a 30-line additive change
  (e.g. find() needs path-compression, but that's a data-structure
  surgery beyond the methodology). Write a defer doc with the
  empirical evidence, commit the doc, update task to completed.

**All three are valid closures.** Refusing to defer just to "keep
trying" is the worst outcome — it stalls the queue.

### Step 4 — Move to next task immediately

The session memory tag `[[feedback-master-role-dispatch]]` says:
"deliverable is the next-task MESSAGE, not long analysis". Same rule
applies to your own queue execution. Don't write 200 lines of analysis
in chat between tasks — the doc you wrote in Step 3 *is* the analysis.

---

## Soundness gate — non-negotiable

Each ship must clear:

1. **Unit tests pass** (`./tests/xolver_unit_tests`).
2. **Lane's regression suite passes** (e.g. NRA reg 151/151).
3. **Paired comparison** with pre-binary on the lane's reg suite.
4. **No new env-string leakage** in the binary if promoting a flag
   (per `[[feedback-no-other-solver-strings]]`).
5. **WSL-safe protocol** observed throughout
   (`[[feedback-wsl-safe-protocol]]`).

If any of these fail, the closure state is REVERT, not SHIP. No
exceptions. A "successful" task with even one violation is technical
debt that returns at Stage 5 ship-prep.

### Pre-existing failures

If the lane's reg surfaces a failure that was already failing under the
pre-binary, the closure is still **track-not-ignore** per
`[[feedback-pre-existing-bugs-tracked]]`: file the bug as a task, route
to the responsible lane, document in the commit message. Don't silently
move on.

---

## Cross-lane application

Phase Z of a queue often includes a **cross-lane direct application**
task: take a methodology shipped on your lane and apply it to another
lane's code. The execution rule:

1. **Find the analog**. NRA's `LibPolyKernel.terms()` (88 sites, pure)
   has analogs in EUF (`RollbackUnionFind::find()`), DT
   (`isFiniteSort`), Array (`representativeStore`). Pick one.
2. **Apply the four-step methodology unchanged**. The methodology IS
   the cross-lane bridge — don't fork it per lane.
3. **Notify the lane owner** if you ship. The Task W commit on
   `agent/nra-2` shipped a DT cache; the DT-lane owner gets a heads-up
   in the commit message (they own the deeper sprint).
4. **Defer cleanly** if your lane's tools don't fit. Task V on EUF
   surfaced a find() optimization that's NOT a 30-line patch — defer
   with empirical evidence for the EUF-deep agent to pick up.

---

## What this session shipped

49 commits on `agent/nra-2` across two long-async-dispatch chains,
all 0-unsound:

* **6-layer hash-cons stack** in `LibPolyKernel`: S1, S1b, S2, S1c, S1d,
  S1e — hit rates 30-98 % on stress, all paired-validated.
* **2 source-flipped flags** (Task Q): LOCALSEARCH + CAC_SR_CACHE
  default-ON, env strings physically removed.
* **NRA reg expansion** 143 → 151 cases: hash-cons + LS-recovery
  regression guards (Task U).
* **First cross-lane ship** (Task W): DT `isFiniteSort` cache,
  62.5-96 % hit rate per case, validates the methodology export.
* **Pattern doc** (`CAMPAIGN-RULES-hash-cons-audit.md`,
  this `CAMPAIGN-RULES-long-async-dispatch.md`).
* **Stage 5 ship-prep audit** (Task Y): 33-flag matrix + 10 diag,
  pre-existing failures tracked.
* **5 defer docs** with empirical evidence for skipped surfaces
  (K bilinear, R cousin, S AlgebraicNumber, T SparseTableau, V EUF).

The defer docs are not failures — they are the methodology working as
designed. They prevent the next session from re-attempting the same
fruitless paths.

---

## Cross-reference

* `docs/CAMPAIGN-RULES-hash-cons-audit.md` — the four-step methodology
  itself. Read this first.
* `docs/WSL-SAFE-PROTOCOL.md` — the local-execution constraints.
* `docs/phase-d/STAGE5-NRA-lane-summary.md` — concrete worked example
  of one lane's full Stage 5 ship-prep matrix.
* `[[feedback-architectural-truth-is-boundary]]` — the rule that
  partial wins ship in sprint mode; architectural boundaries are not
  excuses for skipping clusters.

---

*Branch: `agent/nra-2`. Tip: `c6a03a7` at the time of writing.*
*WSL-safe-protocol observed throughout this session.*
