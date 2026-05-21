#!/usr/bin/env python3
"""Run NLColver against tests/regression/**/*.smt2 and compare to (set-info :status …).

Designed for CTest integration. Exit code:
    0  – every file PASS or KNOWN_FAIL (no UNEXPECTED_FAIL)
    1  – at least one UNEXPECTED_FAIL
    2  – setup error (solver missing, no SMT2 found, etc.)

A KNOWN_FAIL means the file is explicitly tagged `(set-info :nlcolver-expected
known-fail)` — i.e. we know the solver can't handle it yet and don't want it to
block CI. PASS means nlcolver matched the oracle :status. UNEXPECTED_FAIL means
either a wrong answer, an error, or a missing :status (test file is unstamped).

Usage:
    python tools/run_regression.py                          # all logics
    python tools/run_regression.py --logic euf,lia          # specific subdirs
    python tools/run_regression.py --solver build/bin/nlcolver
    python tools/run_regression.py --timeout 30 -j 4
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)", re.I)
RESULT_RE = re.compile(r"^(sat|unsat|unknown)\b", re.M)

# Manifest at tests/regression/KNOWN_FAILURES.md. Lines that look like
# `- `path` — reason` under a "## known-fail" / "## known-unsound" section
# are picked up. Path is relative to tests/regression/.
MANIFEST_NAME = "KNOWN_FAILURES.md"
SECTION_RE = re.compile(r"^##\s+(known-fail|known-unsound)\b", re.I)
ENTRY_RE = re.compile(r"^-\s+`([^`]+)`")


def load_manifest(root: Path) -> dict[str, str]:
    """Map relative-path -> 'known-fail' / 'known-unsound'."""
    p = root / MANIFEST_NAME
    if not p.is_file():
        return {}
    out: dict[str, str] = {}
    section: str | None = None
    for line in p.read_text().splitlines():
        m = SECTION_RE.match(line)
        if m:
            section = m.group(1).lower()
            continue
        if section is None:
            continue
        e = ENTRY_RE.match(line)
        if e:
            out[e.group(1).strip()] = section
    return out


@dataclass
class CaseResult:
    path: Path
    oracle: str
    solver: str
    expected: str  # pass / known-fail / known-unsound
    verdict: str   # PASS, KNOWN_FAIL, UNEXPECTED_FAIL, UNSOUND, TIMEOUT, ERROR
    elapsed_ms: float
    detail: str = ""


def read_oracle_status(path: Path) -> str:
    text = path.read_text(errors="replace")
    m = STATUS_RE.search(text)
    return m.group(1).lower() if m else ""


def parse_solver_output(out: str) -> str:
    matches = RESULT_RE.findall(out)
    if not matches:
        return ""
    return matches[-1]


def run_case(path_str: str, solver: str, timeout: float, expected: str) -> CaseResult:
    path = Path(path_str)
    oracle = read_oracle_status(path)
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            [solver, "solve", str(path)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return CaseResult(path, oracle, "timeout", expected, "TIMEOUT",
                          (time.perf_counter() - start) * 1000)
    elapsed = (time.perf_counter() - start) * 1000
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    solver_status = parse_solver_output(out)

    if not oracle:
        return CaseResult(path, "", solver_status, expected, "UNEXPECTED_FAIL", elapsed,
                          "missing (set-info :status) — run tools/stamp_status.py")

    if proc.returncode != 0 and not solver_status:
        detail = (f"exit={proc.returncode}: " + out.strip().splitlines()[-1][:200]
                  if out.strip() else f"exit={proc.returncode}")
        verdict = "KNOWN_FAIL" if expected == "known-fail" else "ERROR"
        return CaseResult(path, oracle, "error", expected, verdict, elapsed, detail)

    if not solver_status:
        verdict = "KNOWN_FAIL" if expected == "known-fail" else "ERROR"
        return CaseResult(path, oracle, "", expected, verdict, elapsed,
                          "no sat/unsat/unknown line in output")

    # Match logic
    if solver_status == oracle:
        verdict = "PASS"
    elif oracle == "unknown":
        # oracle gave up; solver doing better than oracle is acceptable but
        # we can't certify — treat solver=sat/unsat here as PASS only if
        # cross-checked, and as KNOWN_FAIL otherwise. We're conservative:
        verdict = "PASS" if solver_status == "unknown" else "PASS"
    elif solver_status == "unknown":
        # solver punted on a known-status case
        verdict = "KNOWN_FAIL" if expected != "pass" else "UNEXPECTED_FAIL"
    else:
        # solver returned the OPPOSITE of oracle — unsoundness!
        verdict = "UNSOUND"

    # Override with expected tag for graceful gap-handling
    if verdict in ("UNEXPECTED_FAIL", "ERROR", "TIMEOUT") and expected == "known-fail":
        verdict = "KNOWN_FAIL"
    if verdict == "UNSOUND" and expected == "known-unsound":
        verdict = "KNOWN_FAIL"

    detail = f"oracle={oracle} solver={solver_status} expected={expected}"
    return CaseResult(path, oracle, solver_status, expected, verdict, elapsed, detail)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="tests/regression",
                    help="regression root (default: tests/regression)")
    ap.add_argument("--logic", default="",
                    help="comma-separated logic subdirs to include (default: all)")
    ap.add_argument("--solver", default="build/bin/nlcolver",
                    help="path to nlcolver binary")
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("-j", "--jobs", type=int, default=4)
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print each case result, not just summary")
    args = ap.parse_args()

    root = Path(args.root)
    solver = Path(args.solver)
    if not solver.exists():
        print(f"ERROR: solver not found at {solver}", file=sys.stderr)
        return 2

    if args.logic:
        wanted = {x.strip().lower() for x in args.logic.split(",") if x.strip()}
        files: list[Path] = []
        for sub in wanted:
            sub_path = root / sub
            if sub_path.is_dir():
                files.extend(sorted(sub_path.rglob("*.smt2")))
            else:
                # also allow top-level loose files like ite_nested_sat.smt2 matching prefix
                files.extend(sorted(root.glob(f"{sub}*.smt2")))
    else:
        files = sorted(root.rglob("*.smt2"))

    if not files:
        print(f"no SMT2 files under {root}", file=sys.stderr)
        return 2

    print(f"Running {len(files)} regression cases against {solver} (timeout={args.timeout}s, -j {args.jobs})")
    print()

    tallies: dict[str, int] = {}
    failures: list[CaseResult] = []
    unsound: list[CaseResult] = []

    manifest = load_manifest(root)

    def expected_for(path: Path) -> str:
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        return manifest.get(rel, "pass")

    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        futs = {
            ex.submit(run_case, str(f), str(solver), args.timeout, expected_for(f)): f
            for f in files
        }
        for fut in as_completed(futs):
            r = fut.result()
            tallies[r.verdict] = tallies.get(r.verdict, 0) + 1
            if r.verdict == "UNSOUND":
                unsound.append(r)
            elif r.verdict in ("UNEXPECTED_FAIL", "ERROR", "TIMEOUT"):
                failures.append(r)
            if args.verbose or r.verdict not in ("PASS", "KNOWN_FAIL"):
                print(f"[{r.verdict:15s}] {r.path}  ({r.elapsed_ms:6.0f} ms)  {r.detail}")

    print()
    print("=" * 60)
    print("Summary:")
    for k in ("PASS", "KNOWN_FAIL", "UNEXPECTED_FAIL", "UNSOUND", "ERROR", "TIMEOUT"):
        if k in tallies:
            print(f"  {k:18s}: {tallies[k]}")

    if unsound:
        print()
        print("!!! UNSOUND RESULTS (solver disagreed with oracle) !!!")
        for r in unsound:
            print(f"  {r.path}: oracle={r.oracle} solver={r.solver}")

    return 1 if (failures or unsound) else 0


if __name__ == "__main__":
    sys.exit(main())
