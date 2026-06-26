#!/usr/bin/env python3
"""
compare_solvers.py — per-division competitive scorecard vs z3 / cvc5 / yices.

The north-star metric for "surpassing z3/cvc5/yices" (roadmap #23): not a single
pass/fail number but a PER-LOGIC head-to-head — how many cases each solver
decides, who solves what no one else can (unique), PAR2 time, and Xolver's win/
loss against each rival in every division.

This is the instrument for the server sweep: point it at a benchmark tree, give
it a wall-clock budget, and it prints the scorecard + a JSON dump. It is purely a
measurement tool — it never touches the solver and changes no verdict.

Distinct from tools/run_regression.py (which cross-checks Xolver against z3/cvc5
for SOUNDNESS on the small corpus). Here the question is competitive standing,
and ALL solvers are first-class — but a sat/unsat DISAGREEMENT between any two is
still surfaced loudly, because a rival contradicting Xolver is the cheapest
unsoundness alarm we have.

Usage:
    python3 tools/compare_solvers.py --root <dir> --timeout 20 -j 8
    python3 tools/compare_solvers.py --root benchmarks/QF_NRA --timeout 60 \
            --json /tmp/scorecard.json --limit 200
    python3 tools/compare_solvers.py --root tests/regression --logics nra,nia

Solvers are auto-detected on PATH (z3, cvc5, yices-smt2); Xolver defaults to
build/bin/xolver. Absent rivals are skipped with a note (so the same command
works on a laptop with only z3 and on the full competition box).
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import time
import json
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple

RESULT_RE = re.compile(r"\b(unsat|sat|unknown)\b")
LOGIC_RE = re.compile(r"\(set-logic\s+([A-Za-z0-9_]+)\s*\)")

SOLVED = {"sat", "unsat"}


@dataclass
class SolverSpec:
    name: str            # display name
    argv: List[str]      # base command (binary + fixed flags)
    # Timeout tokens as a function of the budget — a LIST so two-token flags
    # ("--timeout", "10") work as well as single-token ("-T:10").
    timeout_tokens: Optional[object] = None  # Callable[[float], List[str]]
    # Xolver's CLI is `solve <file> [flags]` (flags AFTER the file); rivals take
    # `<flags> <file>`. file_first selects the former.
    file_first: bool = False

    def command(self, smt2: str, timeout_s: float) -> List[str]:
        toks = self.timeout_tokens(timeout_s) if self.timeout_tokens else []
        if self.file_first:
            return list(self.argv) + [smt2] + toks
        return list(self.argv) + toks + [smt2]


def detect_solvers(xolver_path: str) -> List[SolverSpec]:
    """Xolver (required) + every rival found on PATH, with fair native budgets."""
    specs: List[SolverSpec] = []
    if not Path(xolver_path).exists():
        print(f"ERROR: xolver not found at {xolver_path}", file=sys.stderr)
        sys.exit(2)
    sec = lambda t: str(int(max(1, t)))
    # `solve <file> --timeout N`: dogfoods the --timeout flag so Xolver
    # self-aborts to `unknown` within budget rather than being SIGKILLed; either
    # way it counts as "not solved".
    specs.append(SolverSpec("xolver", [xolver_path, "solve"],
                            lambda t: ["--timeout", sec(t)], file_first=True))
    if shutil.which("z3"):
        specs.append(SolverSpec("z3", ["z3", "-smt2"], lambda t: ["-T:" + sec(t)]))
    if shutil.which("cvc5"):
        specs.append(SolverSpec("cvc5", ["cvc5", "--lang=smt2"],
                                lambda t: ["--tlimit=" + str(int(t * 1000))]))
    yices = shutil.which("yices-smt2") or shutil.which("yices")
    if yices:
        specs.append(SolverSpec(Path(yices).name, [yices],
                                lambda t: ["--timeout=" + sec(t)]))
    else:
        print("note: yices-smt2 not on PATH — skipping (install for a full 3-way fight)",
              file=sys.stderr)
    return specs


def parse_verdict(stdout: str, stderr: str) -> str:
    # Take the LAST standalone token (final (check-sat) answer), matching
    # run_regression.py's convention; ignore anything inside (error ...).
    text = (stdout or "") + "\n" + (stderr or "")
    matches = RESULT_RE.findall(text)
    return matches[-1] if matches else ""


def detect_logic(path: Path) -> str:
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return "?"
    m = LOGIC_RE.search(text)
    return m.group(1) if m else "?"


@dataclass
class RunResult:
    file: str
    logic: str
    solver: str
    verdict: str       # sat / unsat / unknown / timeout / error
    elapsed_s: float


def run_one(spec: SolverSpec, smt2: Path, timeout_s: float) -> RunResult:
    logic = detect_logic(smt2)
    start = time.perf_counter()
    # Hard backstop a bit beyond the native budget, in case a solver ignores its
    # own --timeout (so one stuck process can't wedge the whole sweep).
    hard = timeout_s + max(5.0, 0.25 * timeout_s)
    try:
        proc = subprocess.run(
            spec.command(str(smt2), timeout_s),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True, timeout=hard,
        )
    except subprocess.TimeoutExpired:
        return RunResult(str(smt2), logic, spec.name, "timeout", hard)
    except (OSError, ValueError) as e:
        return RunResult(str(smt2), logic, spec.name, "error", time.perf_counter() - start)
    elapsed = time.perf_counter() - start
    verdict = parse_verdict(proc.stdout, proc.stderr)
    if not verdict:
        verdict = "error"
    elif verdict not in SOLVED and verdict != "unknown":
        verdict = "error"
    return RunResult(str(smt2), logic, spec.name, verdict, elapsed)


# --------------------------------------------------------------------------- #
# Aggregation
# --------------------------------------------------------------------------- #
@dataclass
class Tally:
    solved: int = 0
    unique: int = 0
    par2: float = 0.0
    total: int = 0


def aggregate(results: List[RunResult], solver_names: List[str], timeout_s: float):
    # by_file[file] = {solver: RunResult}
    by_file: Dict[str, Dict[str, RunResult]] = defaultdict(dict)
    logic_of: Dict[str, str] = {}
    for r in results:
        by_file[r.file][r.solver] = r
        logic_of[r.file] = r.logic

    # tallies[logic][solver] = Tally ; "ALL" is the cross-logic roll-up
    tallies: Dict[str, Dict[str, Tally]] = defaultdict(lambda: defaultdict(Tally))
    disagreements: List[Tuple[str, Dict[str, str]]] = []

    for f, perslv in by_file.items():
        logic = logic_of[f]
        # Soundness alarm: any sat-vs-unsat split among solvers on this file.
        verds = {s: r.verdict for s, r in perslv.items()}
        decided = {s: v for s, v in verds.items() if v in SOLVED}
        if len(set(decided.values())) > 1:
            disagreements.append((f, verds))
        # Unique solve: exactly one solver decided this file.
        solvers_that_solved = [s for s, v in verds.items() if v in SOLVED]
        uniq = solvers_that_solved[0] if len(solvers_that_solved) == 1 else None
        for s in solver_names:
            r = perslv.get(s)
            for scope in (logic, "ALL"):
                t = tallies[scope][s]
                t.total += 1
                if r and r.verdict in SOLVED:
                    t.solved += 1
                    t.par2 += r.elapsed_s
                    if uniq == s:
                        t.unique += 1
                else:
                    t.par2 += 2.0 * timeout_s
    return tallies, by_file, disagreements


def head_to_head(by_file, ref: str, rival: str) -> Tuple[int, int]:
    """(ref-only wins, rival-only wins): files one decided and the other didn't."""
    ref_win = rival_win = 0
    for perslv in by_file.values():
        rv = perslv.get(ref)
        ov = perslv.get(rival)
        ref_ok = rv and rv.verdict in SOLVED
        ov_ok = ov and ov.verdict in SOLVED
        if ref_ok and not ov_ok:
            ref_win += 1
        elif ov_ok and not ref_ok:
            rival_win += 1
    return ref_win, rival_win


# --------------------------------------------------------------------------- #
# Reporting
# --------------------------------------------------------------------------- #
def print_scorecard(tallies, by_file, solver_names, disagreements, timeout_s):
    ref = solver_names[0]  # xolver
    logics = sorted([k for k in tallies if k != "ALL"]) + ["ALL"]

    w = max(12, max(len(s) for s in solver_names) + 2)
    print("\n" + "=" * 78)
    print("PER-DIVISION SCORECARD  (solved/total, PAR2 seconds — lower is better)")
    print("=" * 78)
    hdr = f"{'logic':<14}" + "".join(f"{s:>{w}}" for s in solver_names)
    print(hdr)
    print("-" * len(hdr))
    for logic in logics:
        row = f"{logic:<14}"
        # best solved-count in this division → mark the leader with '*'
        best = max((tallies[logic][s].solved for s in solver_names), default=0)
        for s in solver_names:
            t = tallies[logic][s]
            mark = "*" if t.solved == best and best > 0 else " "
            cell = f"{t.solved}/{t.total}{mark}"
            row += f"{cell:>{w}}"
        print(row)
    # PAR2 row block
    print("-" * len(hdr))
    print("PAR2 (s):")
    for logic in logics:
        row = f"{logic:<14}"
        best = min((tallies[logic][s].par2 for s in solver_names
                    if tallies[logic][s].total), default=0.0)
        for s in solver_names:
            t = tallies[logic][s]
            mark = "*" if abs(t.par2 - best) < 1e-9 and t.total else " "
            row += f"{t.par2:>{w-1}.1f}{mark}"
        print(row)

    # Unique solves (cases only ONE solver got — the real differentiator)
    print("-" * len(hdr))
    print("UNIQUE solves (only this solver decided it):")
    row = f"{'ALL':<14}"
    for s in solver_names:
        row += f"{tallies['ALL'][s].unique:>{w}}"
    print(row)

    # Head-to-head vs Xolver
    print("\n" + "-" * 78)
    print(f"HEAD-TO-HEAD vs {ref} (across all logics): "
          f"'{ref} wins' = {ref} decided & rival didn't")
    print("-" * 78)
    for rival in solver_names[1:]:
        rw, ow = head_to_head(by_file, ref, rival)
        verdict = ("AHEAD" if rw > ow else "BEHIND" if ow > rw else "EVEN")
        print(f"  {ref} vs {rival:<10}  {ref}-only: {rw:<5}  {rival}-only: {ow:<5}"
              f"  -> {ref} {verdict} (net {rw - ow:+d})")

    # Soundness alarm — loud and last so it can't be missed.
    print("\n" + "-" * 78)
    if disagreements:
        print(f"!!! SAT/UNSAT DISAGREEMENTS: {len(disagreements)} — INVESTIGATE "
              f"(a rival contradicting Xolver is a potential unsoundness) !!!")
        for f, verds in disagreements[:25]:
            joined = "  ".join(f"{s}={v}" for s, v in sorted(verds.items()))
            print(f"  {f}\n      {joined}")
        if len(disagreements) > 25:
            print(f"  ... and {len(disagreements) - 25} more (see --json)")
    else:
        print("Soundness: 0 sat/unsat disagreements across all solvers. OK.")
    print("=" * 78)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", required=True, help="benchmark directory (recursive *.smt2)")
    ap.add_argument("--xolver", default="build/bin/xolver", help="path to xolver binary")
    ap.add_argument("--timeout", type=float, default=20.0, help="per-case wall budget (s)")
    ap.add_argument("-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 1))
    ap.add_argument("--logics", default="",
                    help="comma-separated logic subdir filter (matches path components)")
    ap.add_argument("--limit", type=int, default=0,
                    help="sample at most N files per logic (0 = all) — for quick runs")
    ap.add_argument("--json", default="", help="dump raw per-case results here")
    args = ap.parse_args()

    root = Path(args.root)
    if not root.exists():
        print(f"ERROR: --root {root} does not exist", file=sys.stderr)
        return 2

    files = sorted(root.rglob("*.smt2"))
    if args.logics:
        wanted = {x.strip().lower() for x in args.logics.split(",") if x.strip()}
        files = [f for f in files
                 if any(w in p.lower() for p in f.parts for w in wanted)]
    if args.limit:
        by_logic: Dict[str, List[Path]] = defaultdict(list)
        for f in files:
            by_logic[detect_logic(f)].append(f)
        files = [f for fs in by_logic.values() for f in fs[: args.limit]]
        files.sort()
    if not files:
        print(f"no SMT2 files under {root} (after filters)", file=sys.stderr)
        return 2

    specs = detect_solvers(args.xolver)
    solver_names = [s.name for s in specs]
    print(f"Comparing {len(solver_names)} solvers ({', '.join(solver_names)}) over "
          f"{len(files)} cases, timeout={args.timeout}s, -j {args.jobs}")

    jobs = [(spec, f) for f in files for spec in specs]
    results: List[RunResult] = []
    done = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = [ex.submit(run_one, spec, f, args.timeout) for spec, f in jobs]
        for fut in futs:
            results.append(fut.result())
            done += 1
            if done % 200 == 0:
                print(f"  ... {done}/{len(jobs)} runs", file=sys.stderr)

    tallies, by_file, disagreements = aggregate(results, solver_names, args.timeout)
    print_scorecard(tallies, by_file, solver_names, disagreements, args.timeout)

    if args.json:
        payload = {
            "config": {"root": str(root), "timeout_s": args.timeout,
                       "solvers": solver_names, "cases": len(files)},
            "results": [r.__dict__ for r in results],
            "disagreements": [{"file": f, "verdicts": v} for f, v in disagreements],
        }
        Path(args.json).write_text(json.dumps(payload, indent=2))
        print(f"\nRaw results -> {args.json}")

    # Non-zero exit ONLY on a soundness disagreement (so CI can gate on it).
    return 1 if disagreements else 0


if __name__ == "__main__":
    sys.exit(main())
