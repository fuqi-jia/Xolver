#!/usr/bin/env python3
"""Run Xolver against tests/regression/**/*.smt2 and compare to (set-info :status …).

Designed for CTest integration. Exit code:
    0  – every file PASS or an explicitly allowed incomplete result
    1  – at least one UNEXPECTED_FAIL
    2  – setup error (solver missing, no SMT2 found, etc.)

A KNOWN_FAIL means the file is explicitly tagged `(set-info :xolver-expected
known-fail)` — i.e. we know the solver can't handle it yet and don't want it to
block CI. PASS means xolver matched the oracle :status. UNEXPECTED_FAIL means
either a wrong answer, an error, or a missing :status (test file is unstamped).

Usage:
    python tools/run_regression.py                          # all logics
    python tools/run_regression.py --logic euf,lia          # specific subdirs
    python tools/run_regression.py --solver build/bin/xolver
    python tools/run_regression.py --timeout 30 -j 4
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from pathlib import Path

STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)", re.I)
RESULT_RE = re.compile(r"^(sat|unsat|unknown)[ \t]*$", re.M)

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
        if line.startswith("## "):
            section = None
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
    text = re.sub(r";[^\n]*", "", path.read_text(errors="replace"))
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
            # 3.6-safe (capture_output= / text= are 3.7+).
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return CaseResult(path, oracle, "timeout", expected, "TIMEOUT",
                          (time.perf_counter() - start) * 1000)
    elapsed = (time.perf_counter() - start) * 1000
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    # Diagnostics are never solver answers. In particular, a token on stderr
    # must not overwrite a valid stdout result or turn a crash into a pass.
    solver_status = parse_solver_output(proc.stdout or "")

    if not oracle:
        return CaseResult(path, "", solver_status, expected, "UNEXPECTED_FAIL", elapsed,
                          "missing (set-info :status) — run tools/stamp_status.py")

    # A contradictory answer is always a hard failure, including legacy
    # known-unsound entries and processes that subsequently crash.
    if oracle in ("sat", "unsat") and solver_status in ("sat", "unsat") and solver_status != oracle:
        return CaseResult(path, oracle, solver_status, expected, "UNSOUND", elapsed,
                          f"oracle={oracle} solver={solver_status} exit={proc.returncode}")

    if proc.returncode != 0:
        detail = (f"exit={proc.returncode}: " + out.strip().splitlines()[-1][:200]
                  if out.strip() else f"exit={proc.returncode}")
        return CaseResult(path, oracle, solver_status or "error", expected, "ERROR", elapsed, detail)

    if not solver_status:
        return CaseResult(path, oracle, "", expected, "ERROR", elapsed,
                          "no sat/unsat/unknown line in output")

    # Match logic
    if solver_status == oracle:
        verdict = "PASS"
    elif oracle == "unknown":
        # oracle gave up; solver doing better than oracle is acceptable but
        # we can't certify — treat solver=sat/unsat here as PASS only if
        # cross-checked, and as KNOWN_FAIL otherwise. We're conservative:
        verdict = "UNEXPECTED_FAIL"
    elif solver_status == "unknown":
        # solver punted on a known-status case
        verdict = "KNOWN_FAIL" if expected != "pass" else "UNEXPECTED_FAIL"
    else:
        # solver returned the OPPOSITE of oracle — unsoundness!
        verdict = "UNSOUND"

    detail = f"oracle={oracle} solver={solver_status} expected={expected}"
    return CaseResult(path, oracle, solver_status, expected, verdict, elapsed, detail)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="tests/regression",
                    help="regression root (default: tests/regression)")
    ap.add_argument("--logic", default="",
                    help="comma-separated logic subdirs to include (default: all)")
    ap.add_argument("--solver", default="build/bin/xolver",
                    help="path to xolver binary")
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("-j", "--jobs", type=int, default=4)
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print each case result, not just summary")
    ap.add_argument("--allow-unknown", action="store_true",
                    help="accept unknown for known-gap cases; wrong verdicts and crashes still fail")
    ap.add_argument("--report", type=Path, help="write all per-case outcomes as JSON")
    args = ap.parse_args()

    root = Path(args.root)
    solver = Path(args.solver).resolve()
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
    results: list[CaseResult] = []

    manifest = load_manifest(root)

    def expected_for(path: Path) -> str:
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        return manifest.get(rel, "known-fail" if args.allow_unknown else "pass")

    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        futs = {
            ex.submit(run_case, str(f), str(solver), args.timeout, expected_for(f)): f
            for f in files
        }
        for fut in as_completed(futs):
            r = fut.result()
            results.append(r)
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

    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps({
            "solver": str(solver), "timeout": args.timeout, "jobs": args.jobs,
            "tallies": tallies,
            "cases": [dict(asdict(r), path=str(r.path)) for r in sorted(results, key=lambda r: str(r.path))],
        }, indent=2) + "\n")
    return 1 if (failures or unsound) else 0


if __name__ == "__main__":
    sys.exit(main())
