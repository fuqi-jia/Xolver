# EQ+NIA handoff (2026-06-06) — agent/eqnia @ 4a7848a (PUSHED, ahead=0)

PUSH: origin=https (SSH blocked in WSL); push via `git push origin agent/eqnia` (gh credential helper).
SOLVED 18/89 (UFNIA 15, ANIA 3). Gate: unit 1342, reg 681/682, 0-unsound.

DONE (tractable bugs): d4b83fc bool-atom EUF (00324), 4a7848a bit-blast-early dedup, wall-clock robustness
lane (8e5080c/b52fff5/33e3565/fe677a2/c8719b6), 958e876 array budget, e2aa86c, CMS (30ffdf2/ad34ad3/677b80b).

REMAINING = deep combination engine (full per-root analysis in docs/TASK_LIST.md + docs/nia-eqna-diagnosis.md):
  #4/#5/#6 CLEARSY/Certora sat = model construction at scale (437+ iters x ~18ms; 9 levers ruled out)
  #7/#8 GrandProduct = combination convergence (not a revertible regression)
  #10 ANIA-unsat in-de42 = NIA nonlinear refutation (mul+mod+div, unbounded vars)
  #11 AUFNIA = EUF+arith @ 680KB scale
SUSTAINED EFFORT (authorized): INCREMENTAL THEORY CHECKING (speeds #4/#5/#6/#7/#8/#11).
WARNING: nia-bb-3 perf merge regresses sum10 — cherry-pick its perf commits individually w/ the sum10 gate.
