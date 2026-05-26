# Agent 7 — NIA reasoning stack

**Split from A6 on 2026-05-27.** A6 is now BLAN-bit-blast-only (faithfully porting
BLAN's sign-magnitude bit-blast core, "定死"). A7 takes everything else in NIA — the
reasoning stages, recovery, and combination-NIA conflict work.

| | |
|---|---|
| Branch | `agent/a7-nia-reasoning` |
| Worktree | `../zolver-a7` |
| Base | `integrate-soundness` (has the NIA floor `a2e260a` + the boolpur linkage at `Solver.cpp:533`) |
| Bible | `conversations/5.list/4.chatgpt.nia.md` (the NIA reasoning sections) |
| Owns | `theory/arith/nia` (NiaSolver facade, reasoner stages, preprocess, core), `theory/arith/search`, **and the `nia.bit-blast` stage *wiring*** in NiaSolver (calls A6's backend) |
| Do NOT edit (A6's) | `theory/arith/bit_blast/` (the BitBlast* backend — A6's BLAN port). You wire/call it; you don't change it. |

Common contract in `README.md` (default-OFF `ZOLVER_NIA_*` flags, double gate OFF+ON,
WSL-safe `( ulimit -v 2000000; timeout N cmd )` + `-j1`, anonymous commits, don't merge
to main). Soundness: `CLAUDE.md` invariant 7 — NIA undecidable, SAT ModelValidator-backed,
UNSAT soundly proven, never UNSAT from incomplete reasoning.

## Tasks (priority order)

1. **Presolve OOM — verify before capping.** A6 found the default-path boolpur crash is
   in **bit-blast** (capped by A6's `a96a5e0`), not presolve, and the boolpur linkage is
   already in base (`Solver.cpp:533`). **First confirm:** does A6's bit-blast cap already
   keep the boolpur/QF_NIA-AProVE cases from crashing on the default path (A6 had a scan
   running)? If yes, **A3's `cnf-iff` cherry-pick is unblocked** — tell the master, no
   presolve cap needed. If a presolve OOM still fires, add the bounded-accumulation cap
   (→ sound unknown, never crash).
2. **NIA-357 → correct UNSAT** (`docs/nia-falsesat-routing.md`, all floored sound→unknown by
   A5's `a2e260a` meanwhile): boolpur refutation (linkage already routes the diseq to NIA —
   prove it unsat), NIA-incompleteness (`aproveSMT1072`), soft_float/SVCOMP (the 4 panda1
   false-SATs `soft_float_3a*` — these escape the floor because it's `!hasRealVar`-gated;
   master is flooring them via `VALIDATE_NONLINEAR_SAT`+#11, you recover them to unsat).
3. **UFNIA over-eager Standard-effort conflict** — A3 traced `[CONFLICT-SRC] solver=5
   effort=Standard size=168`: NIA emits an unprovable Standard-effort conflict (invariant-7
   violation → false-UNSAT, floored by `SAT_DEFER_EARLY_CONFLICT`). Make NIA only emit
   conflicts it can prove (defer the rest).
4. **WalkSAT SLS** — cherry-pick `abc5745` from `agent/a2-nonlinear` (A6 stashed it),
   drive toward default-on.
5. **NIA stack audit** vs the bible's minimal-超越集.

## Coordination
- `theory/arith/poly`: **A2 primary** — route poly changes through the master.
- `theory/arith/bit_blast/`: **A6** owns the BLAN backend. You own the `nia.bit-blast`
  stage that *calls* it — coordinate on the backend's API, don't edit the backend itself.
- The NIA validate-sat floor (`a2e260a`) is A5's — build recovery under it.
