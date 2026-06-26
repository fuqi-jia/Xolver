#!/usr/bin/env python3
"""Stamp (set-info :status …) into regression SMT2 files via z3+cvc5 oracle.

Run from repo root:
    python tools/stamp_status.py                  # stamp missing only
    python tools/stamp_status.py --force          # restamp everything
    python tools/stamp_status.py --root tests/regression/euf

Behaviour:
- Skips files that already contain `(set-info :status …)` unless --force.
- For each file: runs z3 and cvc5 with a 10-second timeout each.
- If both agree on sat/unsat -> stamp that status.
- If both return unknown   -> stamp unknown.
- If they disagree         -> stamp unknown + emit a warning line to stderr
  (these are the high-value cases needing human review).
- Insertion point: immediately after the first `(set-logic …)` line, or at
  the top of the file if no set-logic present.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)", re.I)
SET_LOGIC_RE = re.compile(r"^\s*\(\s*set-logic\b", re.M)
RESULT_RE = re.compile(r"^(sat|unsat|unknown)\b", re.M)

ORACLES = [
    ("z3", ["z3", "-smt2"]),
    ("cvc5", ["cvc5", "--lang=smt2"]),
]


@dataclass
class OracleResult:
    name: str
    status: str  # one of: sat, unsat, unknown, error, timeout
    note: str = ""


def run_oracle(name: str, argv: list[str], path: Path, timeout: float) -> OracleResult:
    try:
        proc = subprocess.run(
            argv + [str(path)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return OracleResult(name, "timeout")
    except FileNotFoundError:
        return OracleResult(name, "error", f"{name} not installed")
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    matches = RESULT_RE.findall(out)
    if not matches:
        return OracleResult(name, "error", out.strip()[:120])
    return OracleResult(name, matches[-1])


def decide(results: list[OracleResult]) -> tuple[str, str]:
    """Returns (final_status, note). final_status in sat/unsat/unknown."""
    answers = {r.status for r in results if r.status in {"sat", "unsat", "unknown"}}
    sat_unsat = answers & {"sat", "unsat"}
    if len(sat_unsat) == 2:
        return "unknown", "disagreement: " + ",".join(f"{r.name}={r.status}" for r in results)
    if len(sat_unsat) == 1:
        return next(iter(sat_unsat)), ""
    # no concrete answer; either all unknown/error/timeout
    return "unknown", "no oracle concluded: " + ",".join(f"{r.name}={r.status}" for r in results)


def stamp_file(path: Path, status: str, comment: str) -> None:
    text = path.read_text()
    info_line = f"(set-info :status {status})"
    if comment:
        info_line = f"; oracle: {comment}\n" + info_line
    m = SET_LOGIC_RE.search(text)
    if m:
        end = text.find("\n", m.end())
        if end == -1:
            new_text = text + "\n" + info_line + "\n"
        else:
            new_text = text[: end + 1] + info_line + "\n" + text[end + 1 :]
    else:
        new_text = info_line + "\n" + text
    path.write_text(new_text)


def already_stamped(path: Path) -> bool:
    return STATUS_RE.search(path.read_text()) is not None


def process_one(path: Path, timeout: float, force: bool) -> tuple[Path, str, str]:
    if not force and already_stamped(path):
        return path, "skip", "already stamped"
    results = [run_oracle(name, argv, path, timeout) for name, argv in ORACLES]
    final, note = decide(results)
    stamp_file(path, final, note)
    return path, final, note


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="tests/regression", help="directory to scan")
    ap.add_argument("--timeout", type=float, default=10.0, help="oracle timeout seconds")
    ap.add_argument("-j", "--jobs", type=int, default=8, help="parallel workers")
    ap.add_argument("--force", action="store_true", help="restamp even if :status present")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    root = Path(args.root)
    files = sorted(root.rglob("*.smt2"))
    if not files:
        print(f"no SMT2 files under {root}", file=sys.stderr)
        return 1

    if args.dry_run:
        for f in files:
            tag = "stamped" if already_stamped(f) else "missing"
            print(f"{tag}\t{f}")
        return 0

    by_status: dict[str, int] = {"sat": 0, "unsat": 0, "unknown": 0, "skip": 0}
    warnings: list[str] = []

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(process_one, f, args.timeout, args.force): f for f in files}
        for fut in as_completed(futs):
            path, status, note = fut.result()
            by_status[status] = by_status.get(status, 0) + 1
            tag = status.upper()
            if note:
                warnings.append(f"{path}: {note}")
            print(f"[{tag:7s}] {path}{(' :: ' + note) if note else ''}")

    print()
    print("Summary:")
    for k in ("sat", "unsat", "unknown", "skip"):
        print(f"  {k:7s}: {by_status.get(k, 0)}")
    if warnings:
        print(f"\n{len(warnings)} files need human review (disagreement or no conclusion):")
        for w in warnings:
            print(f"  - {w}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
