#!/usr/bin/env python3
"""
NLColver Benchmark Runner

One-click benchmark runner for NLColver with optional cross-checking against Z3.

Usage:
    # Run NLColver on QF_LRA with 8 threads, 30s timeout per instance
    python tools/run_benchmark.py --logic QF_LRA -j 8 -t 30

    # Run and compare with Z3
    python tools/run_benchmark.py --logic QF_LRA -j 8 -t 30 --compare-with z3

    # Run in background
    nohup python tools/run_benchmark.py --logic QF_NIA -j 4 -t 60 --compare-with z3 > benchmark_run.log 2>&1 &

    # Quick test on 100 files
    python tools/run_benchmark.py --logic QF_LRA -j 8 -t 10 --max-files 100

    # Filter specific sub-directory
    python tools/run_benchmark.py --logic QF_LIA -j 8 -t 30 --filter 2023
"""

import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# =============================================================================
# Configuration
# =============================================================================

BENCHMARK_ROOT = Path("benchmark/non-incremental")
DEFAULT_SOLVER = "./build/bin/nlcolver"
RESULT_PATTERNS = [
    (r"\bunsat\b", "unsat"),
    (r"\bsat\b", "sat"),
    (r"\bunknown\b", "unknown"),
    (r"\berror\b", "error"),
]

# Map shorthand logic names to full QF_* names
LOGIC_ALIASES = {
    "lra": "QF_LRA",
    "lia": "QF_LIA",
    "lira": "QF_LIRA",
    "nra": "QF_NRA",
    "nia": "QF_NIA",
    "nira": "QF_NIRA",
    "idl": "QF_IDL",
    "rdl": "QF_RDL",
    "uf": "QF_UF",
    "uflia": "QF_UFLIA",
    "uflra": "QF_UFLRA",
    "ufnia": "QF_UFNIA",
    "ufnra": "QF_UFNRA",
    "bool": "QF_BOOL",
}


# =============================================================================
# Data structures
# =============================================================================

@dataclass
class RunResult:
    file: str
    result: str          # sat | unsat | unknown | timeout | error | killed
    elapsed: float
    stdout: str = ""
    stderr: str = ""
    returncode: int = 0
    solver: str = "nlcolver"


@dataclass
class ComparisonRow:
    file: str
    nlcolver_result: str
    nlcolver_time: float
    compare_result: str
    compare_time: float
    match: str           # MATCH | MISMATCH | DIFF | SKIP
    note: str = ""


@dataclass
class Statistics:
    logic: str
    total_files: int
    nlcolver: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    compare: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    mismatches: int = 0
    diffs: int = 0
    total_time_nlcolver: float = 0.0
    total_time_compare: float = 0.0
    avg_time_nlcolver: float = 0.0
    avg_time_compare: float = 0.0
    max_time_nlcolver: float = 0.0
    max_time_compare: float = 0.0
    category_stats: Dict[str, Dict] = field(default_factory=dict)


# =============================================================================
# Utilities
# =============================================================================

def resolve_logic(name: str) -> str:
    """Resolve logic name to full QF_* form."""
    upper = name.upper()
    if upper.startswith("QF_"):
        return upper
    lower = name.lower()
    if lower in LOGIC_ALIASES:
        return LOGIC_ALIASES[lower]
    # Try common prefixes
    for prefix in ["QF_", ""]:
        candidate = prefix + upper
        path = BENCHMARK_ROOT / candidate
        if path.exists():
            return candidate
    raise ValueError(f"Unknown logic: {name}. Available: {', '.join(list_logic_dirs())}")


def list_logic_dirs() -> List[str]:
    """List available logic directories."""
    if not BENCHMARK_ROOT.exists():
        return []
    return sorted([d.name for d in BENCHMARK_ROOT.iterdir() if d.is_dir()])


def find_smt2_files(logic: str, filter_str: Optional[str] = None, max_files: Optional[int] = None) -> List[Path]:
    """Find all .smt2 files for a given logic."""
    logic_dir = BENCHMARK_ROOT / logic
    if not logic_dir.exists():
        raise FileNotFoundError(f"Benchmark directory not found: {logic_dir}")

    files = []
    for f in logic_dir.rglob("*.smt2"):
        rel = f.relative_to(logic_dir)
        if filter_str and filter_str not in str(rel):
            continue
        files.append(f)

    files.sort()
    if max_files is not None and max_files > 0:
        files = files[:max_files]
    return files


def parse_result(stdout: str, stderr: str, returncode: int, timed_out: bool = False) -> str:
    """Extract sat/unsat/unknown/error from solver output."""
    if timed_out:
        return "timeout"

    # Check for OOM killer or signals
    if returncode == -9 or returncode == 137:
        return "killed"
    if returncode != 0 and "error" in (stdout + stderr).lower():
        # Some solvers exit non-zero on error
        pass

    combined = stdout + "\n" + stderr
    lines = combined.strip().splitlines()

    # Scan from the bottom (result usually at the end)
    for line in reversed(lines):
        line_stripped = line.strip().lower()
        # Skip lines that are clearly not standalone results
        if not line_stripped or line_stripped.startswith("("):
            continue
        for pattern, result in RESULT_PATTERNS:
            if re.search(pattern, line_stripped):
                return result

    # Fallback: if returncode != 0 and we didn't match anything
    if returncode != 0:
        if "timeout" in combined.lower():
            return "timeout"
        return "error"

    return "unknown"


def run_solver(cmd: List[str], file_path: Path, timeout: float, solver_name: str = "solver", extra_args: Optional[List[str]] = None) -> RunResult:
    """Run a single solver on a single file."""
    start = time.perf_counter()
    timed_out = False
    full_cmd = cmd + [str(file_path)]
    if extra_args:
        full_cmd += extra_args
    try:
        proc = subprocess.run(
            full_cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        elapsed = time.perf_counter() - start
        result = parse_result(proc.stdout, proc.stderr, proc.returncode, timed_out=False)
        return RunResult(
            file=str(file_path),
            result=result,
            elapsed=elapsed,
            stdout=proc.stdout,
            stderr=proc.stderr,
            returncode=proc.returncode,
            solver=solver_name,
        )
    except subprocess.TimeoutExpired as e:
        elapsed = time.perf_counter() - start
        return RunResult(
            file=str(file_path),
            result="timeout",
            elapsed=elapsed,
            stdout=e.stdout or "",
            stderr=e.stderr or "",
            returncode=-1,
            solver=solver_name,
        )
    except Exception as e:
        elapsed = time.perf_counter() - start
        return RunResult(
            file=str(file_path),
            result="error",
            elapsed=elapsed,
            stdout="",
            stderr=str(e),
            returncode=-2,
            solver=solver_name,
        )


def run_nlcolver(file_path: Path, solver_path: str, timeout: float, logic: Optional[str] = None) -> RunResult:
    cmd = [solver_path, "solve"]
    # Note: options must come AFTER the file path for this CLI parser
    return run_solver(cmd, file_path, timeout, solver_name="nlcolver", extra_args=["--logic", logic] if logic else None)


def run_compare(file_path: Path, compare_solver: str, timeout: float) -> RunResult:
    cmd = [compare_solver]
    return run_solver(cmd, file_path, timeout, solver_name=compare_solver)


def compare_results(nlcolver: RunResult, compare: RunResult) -> Tuple[str, str]:
    """
    Compare two results.
    Returns: (match_status, note)
    """
    n = nlcolver.result
    c = compare.result

    # Exact match
    if n == c:
        return "MATCH", ""

    # Both are some form of "no answer"
    no_answer = {"timeout", "unknown", "killed", "error"}
    if n in no_answer and c in no_answer:
        return "DIFF", f"both non-answer: {n} vs {c}"

    # One is definitive, the other is not
    definitive = {"sat", "unsat"}
    if n in definitive and c in no_answer:
        return "DIFF", f"nlcolver={n}, compare={c}"
    if c in definitive and n in no_answer:
        return "DIFF", f"nlcolver={n}, compare={c}"

    # sat vs unsat -> serious mismatch
    if (n == "sat" and c == "unsat") or (n == "unsat" and c == "sat"):
        return "MISMATCH", f"nlcolver={n}, compare={c}"

    return "DIFF", f"nlcolver={n}, compare={c}"


# =============================================================================
# Reporting
# =============================================================================

def write_summary(output_dir: Path, stats: Statistics, args, duration: float):
    summary_path = output_dir / "summary.txt"
    with open(summary_path, "w") as f:
        f.write("=" * 70 + "\n")
        f.write("NLColver Benchmark Report\n")
        f.write("=" * 70 + "\n\n")
        f.write(f"Date:           {datetime.now().isoformat()}\n")
        f.write(f"Logic:          {stats.logic}\n")
        f.write(f"Benchmark root: {BENCHMARK_ROOT}\n")
        f.write(f"NLColver:       {args.solver}\n")
        if args.compare_with:
            f.write(f"Compare with:   {args.compare_with}\n")
        f.write(f"Jobs:           {args.jobs}\n")
        f.write(f"Timeout:        {args.timeout}s\n")
        f.write(f"Total files:    {stats.total_files}\n")
        f.write(f"Wall-clock:     {duration:.2f}s\n")
        f.write("\n")

        f.write("-" * 70 + "\n")
        f.write("NLColver Results\n")
        f.write("-" * 70 + "\n")
        for res in ["sat", "unsat", "unknown", "timeout", "error", "killed"]:
            cnt = stats.nlcolver.get(res, 0)
            pct = cnt / stats.total_files * 100 if stats.total_files else 0
            f.write(f"  {res:12s}: {cnt:6d} ({pct:5.1f}%)\n")
        f.write(f"  {'Total time':12s}: {stats.total_time_nlcolver:10.2f}s\n")
        f.write(f"  {'Avg time':12s}: {stats.avg_time_nlcolver:10.2f}s\n")
        f.write(f"  {'Max time':12s}: {stats.max_time_nlcolver:10.2f}s\n")
        f.write("\n")

        if args.compare_with:
            f.write("-" * 70 + "\n")
            f.write(f"{args.compare_with} Results\n")
            f.write("-" * 70 + "\n")
            for res in ["sat", "unsat", "unknown", "timeout", "error", "killed"]:
                cnt = stats.compare.get(res, 0)
                pct = cnt / stats.total_files * 100 if stats.total_files else 0
                f.write(f"  {res:12s}: {cnt:6d} ({pct:5.1f}%)\n")
            f.write(f"  {'Total time':12s}: {stats.total_time_compare:10.2f}s\n")
            f.write(f"  {'Avg time':12s}: {stats.avg_time_compare:10.2f}s\n")
            f.write(f"  {'Max time':12s}: {stats.max_time_compare:10.2f}s\n")
            f.write("\n")

            f.write("-" * 70 + "\n")
            f.write("Comparison\n")
            f.write("-" * 70 + "\n")
            f.write(f"  MATCH:     {stats.total_files - stats.mismatches - stats.diffs}\n")
            f.write(f"  DIFF:      {stats.diffs}\n")
            f.write(f"  MISMATCH:  {stats.mismatches}  {'***' if stats.mismatches > 0 else ''}\n")
            f.write("\n")

        f.write("=" * 70 + "\n")
    print(f"[Summary written to {summary_path}]")


def write_csv(output_dir: Path, rows: List[ComparisonRow]):
    csv_path = output_dir / "results.csv"
    with open(csv_path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "file", "nlcolver_result", "nlcolver_time",
            "compare_result", "compare_time", "match", "note"
        ])
        for r in rows:
            writer.writerow([
                r.file, r.nlcolver_result, f"{r.nlcolver_time:.3f}",
                r.compare_result, f"{r.compare_time:.3f}", r.match, r.note
            ])
    print(f"[CSV written to {csv_path}]")


def write_discrepancies(output_dir: Path, rows: List[ComparisonRow]):
    mismatches = [r for r in rows if r.match == "MISMATCH"]
    diffs = [r for r in rows if r.match == "DIFF"]

    path = output_dir / "discrepancies.txt"
    with open(path, "w") as f:
        f.write("=" * 70 + "\n")
        f.write(f"MISMATCHES (sat vs unsat): {len(mismatches)}\n")
        f.write("=" * 70 + "\n")
        for r in mismatches:
            f.write(f"\n{r.file}\n")
            f.write(f"  nlcolver: {r.nlcolver_result} ({r.nlcolver_time:.3f}s)\n")
            f.write(f"  compare:  {r.compare_result} ({r.compare_time:.3f}s)\n")
            f.write(f"  note:     {r.note}\n")

        f.write("\n" + "=" * 70 + "\n")
        f.write(f"DIFFS (other disagreements): {len(diffs)}\n")
        f.write("=" * 70 + "\n")
        for r in diffs:
            f.write(f"\n{r.file}\n")
            f.write(f"  nlcolver: {r.nlcolver_result} ({r.nlcolver_time:.3f}s)\n")
            f.write(f"  compare:  {r.compare_result} ({r.compare_time:.3f}s)\n")
            f.write(f"  note:     {r.note}\n")
    print(f"[Discrepancies written to {path}]")


def write_errors(output_dir: Path, nlcolver_results: List[RunResult], compare_results: Optional[List[RunResult]]):
    path = output_dir / "errors.txt"
    with open(path, "w") as f:
        f.write("=" * 70 + "\n")
        f.write("NLColver Errors / Timeouts / Killed\n")
        f.write("=" * 70 + "\n")
        for r in nlcolver_results:
            if r.result in ("error", "timeout", "killed"):
                f.write(f"\n{r.file}\n")
                f.write(f"  result: {r.result} ({r.elapsed:.3f}s)\n")
                if r.stderr.strip():
                    f.write(f"  stderr: {r.stderr[:500]}\n")

        if compare_results:
            f.write("\n" + "=" * 70 + "\n")
            f.write(f"Compare Solver Errors / Timeouts / Killed\n")
            f.write("=" * 70 + "\n")
            for r in compare_results:
                if r.result in ("error", "timeout", "killed"):
                    f.write(f"\n{r.file}\n")
                    f.write(f"  result: {r.result} ({r.elapsed:.3f}s)\n")
                    if r.stderr.strip():
                        f.write(f"  stderr: {r.stderr[:500]}\n")
    print(f"[Errors written to {path}]")


def write_json_stats(output_dir: Path, stats: Statistics, rows: List[ComparisonRow]):
    path = output_dir / "statistics.json"
    # Build stats dict manually because asdict() cannot serialize defaultdict
    stats_dict = {
        "logic": stats.logic,
        "total_files": stats.total_files,
        "nlcolver": dict(stats.nlcolver),
        "compare": dict(stats.compare),
        "mismatches": stats.mismatches,
        "diffs": stats.diffs,
        "total_time_nlcolver": stats.total_time_nlcolver,
        "total_time_compare": stats.total_time_compare,
        "avg_time_nlcolver": stats.avg_time_nlcolver,
        "avg_time_compare": stats.avg_time_compare,
        "max_time_nlcolver": stats.max_time_nlcolver,
        "max_time_compare": stats.max_time_compare,
        "category_stats": {
            cat: {
                "count": cstat["count"],
                "nlcolver": dict(cstat["nlcolver"]),
                "compare": dict(cstat.get("compare", {})),
                "mismatches": cstat["mismatches"],
                "diffs": cstat["diffs"],
            }
            for cat, cstat in stats.category_stats.items()
        },
    }
    data = {
        "meta": {
            "date": datetime.now().isoformat(),
            "logic": stats.logic,
        },
        "statistics": stats_dict,
        "results": [asdict(r) for r in rows],
    }
    with open(path, "w") as f:
        json.dump(data, f, indent=2)
    print(f"[JSON stats written to {path}]")


def write_top_slow(output_dir: Path, rows: List[ComparisonRow], n: int = 50):
    path = output_dir / "top_slow.txt"
    with open(path, "w") as f:
        f.write("=" * 70 + "\n")
        f.write(f"Top {n} Slowest NLColver Runs\n")
        f.write("=" * 70 + "\n")
        sorted_rows = sorted(rows, key=lambda r: r.nlcolver_time, reverse=True)
        for i, r in enumerate(sorted_rows[:n], 1):
            f.write(f"{i:3d}. {r.nlcolver_time:8.3f}s  {r.file}\n")

        f.write("\n" + "=" * 70 + "\n")
        f.write(f"Top {n} Slowest Compare Runs\n")
        f.write("=" * 70 + "\n")
        sorted_rows = sorted(rows, key=lambda r: r.compare_time, reverse=True)
        for i, r in enumerate(sorted_rows[:n], 1):
            f.write(f"{i:3d}. {r.compare_time:8.3f}s  {r.file}\n")
    print(f"[Top slow written to {path}]")


def write_html_report(output_dir: Path, stats: Statistics, rows: List[ComparisonRow], args, wall_time: float):
    path = output_dir / "report.html"

    # Prepare data payload for JS
    top_n = 50
    sorted_nlc = sorted(rows, key=lambda r: r.nlcolver_time, reverse=True)[:top_n]
    sorted_cmp = sorted(rows, key=lambda r: r.compare_time, reverse=True)[:top_n]

    data = {
        "meta": {
            "date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "logic": stats.logic,
            "totalFiles": stats.total_files,
            "jobs": args.jobs,
            "timeout": args.timeout,
            "solver": args.solver,
            "compareWith": args.compare_with,
            "wallTime": round(wall_time, 2),
            "hasCompare": bool(args.compare_with),
        },
        "nlcolver": {
            "sat": stats.nlcolver.get("sat", 0),
            "unsat": stats.nlcolver.get("unsat", 0),
            "unknown": stats.nlcolver.get("unknown", 0),
            "timeout": stats.nlcolver.get("timeout", 0),
            "error": stats.nlcolver.get("error", 0),
            "killed": stats.nlcolver.get("killed", 0),
            "totalTime": round(stats.total_time_nlcolver, 2),
            "avgTime": round(stats.avg_time_nlcolver, 3),
            "maxTime": round(stats.max_time_nlcolver, 3),
        },
        "compare": {
            "sat": stats.compare.get("sat", 0),
            "unsat": stats.compare.get("unsat", 0),
            "unknown": stats.compare.get("unknown", 0),
            "timeout": stats.compare.get("timeout", 0),
            "error": stats.compare.get("error", 0),
            "killed": stats.compare.get("killed", 0),
            "totalTime": round(stats.total_time_compare, 2),
            "avgTime": round(stats.avg_time_compare, 3),
            "maxTime": round(stats.max_time_compare, 3),
        } if args.compare_with else None,
        "mismatches": stats.mismatches,
        "diffs": stats.diffs,
        "rows": [
            {
                "file": r.file,
                "nlcolverResult": r.nlcolver_result,
                "nlcolverTime": round(r.nlcolver_time, 3),
                "compareResult": r.compare_result,
                "compareTime": round(r.compare_time, 3),
                "match": r.match,
                "note": r.note,
            }
            for r in rows
        ],
        "categoryStats": [
            {
                "name": cat,
                "count": cstat["count"],
                "nlcolver": dict(cstat["nlcolver"]),
                "compare": dict(cstat.get("compare", {})),
                "mismatches": cstat.get("mismatches", 0),
                "diffs": cstat.get("diffs", 0),
            }
            for cat, cstat in sorted(stats.category_stats.items())
        ],
        "topSlowNlc": [
            {"file": r.file, "time": round(r.nlcolver_time, 3)}
            for r in sorted_nlc
        ],
        "topSlowCmp": [
            {"file": r.file, "time": round(r.compare_time, 3)}
            for r in sorted_cmp
        ],
    }
    data_json = json.dumps(data, ensure_ascii=False, separators=(",", ":"))

    html = _HTML_TEMPLATE.replace("__DATA_JSON__", data_json)
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    print(f"[HTML report written to {path}]")


_HTML_TEMPLATE = r'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>NLColver Benchmark Report</title>
<style>
:root {
  --c-sat: #10b981; --c-unsat: #ef4444; --c-unknown: #9ca3af;
  --c-timeout: #f59e0b; --c-error: #8b5cf6; --c-killed: #4b5563;
  --c-match: #10b981; --c-mismatch: #ef4444; --c-diff: #f59e0b;
  --bg: #f1f5f9; --card: #ffffff; --text: #1e293b; --muted: #64748b;
  --border: #e2e8f0; --shadow: 0 4px 6px -1px rgba(0,0,0,0.05), 0 2px 4px -2px rgba(0,0,0,0.05);
  --radius: 12px;
}
* { box-sizing: border-box; }
body { margin:0; font-family: -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif; background:var(--bg); color:var(--text); line-height:1.5; }
header { background: linear-gradient(135deg,#0f172a,#1e293b); color:#fff; padding:40px 24px 32px; text-align:center; }
header h1 { margin:0 0 8px; font-size:2rem; letter-spacing:-0.5px; }
header p { margin:0; opacity:.75; font-size:.95rem; }
.badge { display:inline-block; padding:3px 10px; border-radius:999px; font-size:.78rem; font-weight:600; text-transform:uppercase; letter-spacing:.4px; }
.badge-sat { background:rgba(16,185,129,.12); color:#047857; }
.badge-unsat { background:rgba(239,68,68,.12); color:#b91c1c; }
.badge-unknown { background:rgba(156,163,175,.15); color:#4b5563; }
.badge-timeout { background:rgba(245,158,11,.12); color:#b45309; }
.badge-error { background:rgba(139,92,246,.12); color:#6d28d9; }
.badge-killed { background:rgba(75,85,99,.12); color:#1f2937; }
.badge-match { background:rgba(16,185,129,.12); color:#047857; }
.badge-mismatch { background:rgba(239,68,68,.2); color:#991b1b; animation:pulse 2s infinite; }
.badge-diff { background:rgba(245,158,11,.15); color:#92400e; }
@keyframes pulse { 0%,100%{box-shadow:0 0 0 0 rgba(239,68,68,.35);} 50%{box-shadow:0 0 0 8px rgba(239,68,68,0);} }
main { max-width:1400px; margin:0 auto; padding:24px; }
.grid { display:grid; gap:20px; }
.cols-4 { grid-template-columns:repeat(4,1fr); }
.cols-3 { grid-template-columns:repeat(3,1fr); }
.cols-2 { grid-template-columns:repeat(2,1fr); }
@media (max-width:1100px){ .cols-4{grid-template-columns:repeat(2,1fr);} }
@media (max-width:720px){ .cols-4,.cols-3,.cols-2{grid-template-columns:1fr;} }
.card { background:var(--card); border-radius:var(--radius); box-shadow:var(--shadow); padding:20px; border:1px solid var(--border); }
.card h2 { margin:0 0 14px; font-size:1.1rem; display:flex; align-items:center; gap:8px; }
.card h2 .dot { width:10px; height:10px; border-radius:50%; display:inline-block; }
.stat-grid { display:grid; grid-template-columns:repeat(3,1fr); gap:12px; text-align:center; }
.stat-item .value { font-size:1.6rem; font-weight:700; }
.stat-item .label { font-size:.8rem; color:var(--muted); margin-top:2px; }
.metric-row { display:flex; justify-content:space-between; padding:6px 0; border-bottom:1px dashed var(--border); font-size:.9rem; }
.metric-row:last-child { border-bottom:none; }
.chart-wrap { display:flex; align-items:center; justify-content:center; flex-direction:column; gap:12px; }
.chart-legend { display:flex; flex-wrap:wrap; gap:10px 16px; justify-content:center; font-size:.8rem; }
.legend-dot { width:10px; height:10px; border-radius:50%; display:inline-block; margin-right:4px; }
table { width:100%; border-collapse:collapse; font-size:.88rem; }
th, td { padding:10px 12px; text-align:left; border-bottom:1px solid var(--border); }
th { background:#f8fafc; font-weight:600; color:var(--muted); font-size:.8rem; text-transform:uppercase; letter-spacing:.4px; position:sticky; top:0; z-index:2; }
tr:hover td { background:#f8fafc; }
.filter-bar { display:flex; gap:10px; flex-wrap:wrap; margin-bottom:14px; align-items:center; }
.filter-bar input, .filter-bar button { padding:8px 14px; border-radius:8px; border:1px solid var(--border); font-size:.85rem; outline:none; }
.filter-bar input { flex:1; min-width:200px; }
.filter-bar button { background:#fff; cursor:pointer; transition:.15s; }
.filter-bar button.active { background:#0f172a; color:#fff; border-color:#0f172a; }
.filter-bar button:hover:not(.active) { background:#f1f5f9; }
.section { margin-top:28px; }
.section-title { font-size:1.25rem; font-weight:700; margin-bottom:16px; display:flex; align-items:center; gap:10px; }
.mismatch-card { border-left:4px solid var(--c-mismatch); background:#fef2f2; padding:14px 16px; border-radius:0 8px 8px 0; margin-bottom:10px; }
.mismatch-card .title { font-weight:600; font-size:.9rem; margin-bottom:4px; }
.mismatch-card .sub { font-size:.82rem; color:var(--muted); }
.scroll-table { max-height:520px; overflow:auto; border-radius:8px; border:1px solid var(--border); }
.empty { text-align:center; padding:40px; color:var(--muted); font-size:.9rem; }
.footer { text-align:center; padding:30px; color:var(--muted); font-size:.8rem; }
.bar-chart { display:flex; align-items:flex-end; gap:6px; height:140px; padding:10px 0; }
.bar-item { flex:1; display:flex; flex-direction:column; align-items:center; gap:4px; min-width:24px; }
.bar-fill { width:100%; border-radius:4px 4px 0 0; background:#cbd5e1; transition:height .4s ease; }
.bar-label { font-size:.65rem; color:var(--muted); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:100%; }
.bar-value { font-size:.7rem; font-weight:600; }
</style>
</head>
<body>
<header>
  <h1>NLColver Benchmark Report</h1>
  <p id="subtitle">Loading...</p>
</header>

<main>
  <!-- Overview -->
  <section class="grid cols-4" id="overview"></section>

  <!-- Charts -->
  <section class="grid cols-2 section" id="charts"></section>

  <!-- Time Metrics -->
  <section class="grid cols-2 section" id="metrics"></section>

  <!-- Full Table -->
  <section class="section">
    <div class="section-title">📋 Detailed Results <span id="table-count"></span></div>
    <div class="card">
      <div class="filter-bar">
        <input type="text" id="search" placeholder="Search filename...">
        <button class="active" data-filter="all">All</button>
        <button data-filter="MATCH">Match</button>
        <button data-filter="MISMATCH">Mismatch</button>
        <button data-filter="DIFF">Diff</button>
        <button data-filter="sat">SAT</button>
        <button data-filter="unsat">UNSAT</button>
        <button data-filter="timeout">Timeout</button>
        <button data-filter="error">Error</button>
      </div>
      <div class="scroll-table">
        <table id="results-table">
          <thead><tr id="table-head"></tr></thead>
          <tbody id="table-body"></tbody>
        </table>
      </div>
    </div>
  </section>

  <!-- Anomalies -->
  <section class="section" id="anomalies"></section>

  <!-- Categories -->
  <section class="section" id="categories"></section>

  <!-- Top Slow -->
  <section class="section" id="topslow"></section>
</main>

<div class="footer">Generated by NLColver Benchmark Runner</div>

<script>
const DATA = __DATA_JSON__;

const COLORS = {
  sat:'#10b981', unsat:'#ef4444', unknown:'#9ca3af', timeout:'#f59e0b', error:'#8b5cf6', killed:'#4b5563'
};
const LABELS = {sat:'SAT', unsat:'UNSAT', unknown:'Unknown', timeout:'Timeout', error:'Error', killed:'Killed'};

function badge(cls, text) { return `<span class="badge badge-${cls}">${text}</span>`; }

function renderOverview() {
  const m = DATA.meta;
  const n = DATA.nlcolver;
  const c = DATA.compare;
  let html = '';

  // Total files
  html += `<div class="card"><h2><span class="dot" style="background:#0f172a"></span>Files</h2>
    <div class="stat-grid"><div class="stat-item"><div class="value">${m.totalFiles}</div><div class="label">Total</div></div>
    <div class="stat-item"><div class="value">${m.jobs}</div><div class="label">Threads</div></div>
    <div class="stat-item"><div class="value">${m.timeout}s</div><div class="label">Timeout</div></div></div></div>`;

  // NLColver summary
  html += `<div class="card"><h2><span class="dot" style="background:#3b82f6"></span>NLColver</h2>
    <div class="stat-grid">
      <div class="stat-item"><div class="value" style="color:${COLORS.sat}">${n.sat}</div><div class="label">SAT</div></div>
      <div class="stat-item"><div class="value" style="color:${COLORS.unsat}">${n.unsat}</div><div class="label">UNSAT</div></div>
      <div class="stat-item"><div class="value" style="color:${COLORS.timeout}">${n.timeout}</div><div class="label">T/O</div></div>
    </div></div>`;

  // Compare summary
  if (c) {
    html += `<div class="card"><h2><span class="dot" style="background:#f59e0b"></span>${m.compareWith}</h2>
      <div class="stat-grid">
        <div class="stat-item"><div class="value" style="color:${COLORS.sat}">${c.sat}</div><div class="label">SAT</div></div>
        <div class="stat-item"><div class="value" style="color:${COLORS.unsat}">${c.unsat}</div><div class="label">UNSAT</div></div>
        <div class="stat-item"><div class="value" style="color:${COLORS.timeout}">${c.timeout}</div><div class="label">T/O</div></div>
      </div></div>`;

    // Mismatch
    const misColor = DATA.mismatches > 0 ? 'var(--c-mismatch)' : 'var(--c-match)';
    html += `<div class="card"><h2><span class="dot" style="background:${misColor}"></span>Comparison</h2>
      <div class="stat-grid">
        <div class="stat-item"><div class="value" style="color:var(--c-match)">${m.totalFiles - DATA.mismatches - DATA.diffs}</div><div class="label">Match</div></div>
        <div class="stat-item"><div class="value" style="color:var(--c-diff)">${DATA.diffs}</div><div class="label">Diff</div></div>
        <div class="stat-item"><div class="value" style="color:${misColor}">${DATA.mismatches}</div><div class="label">Mismatch</div></div>
      </div></div>`;
  } else {
    html += `<div class="card"><h2><span class="dot" style="background:#64748b"></span>Time</h2>
      <div class="stat-grid">
        <div class="stat-item"><div class="value">${n.totalTime}s</div><div class="label">Total</div></div>
        <div class="stat-item"><div class="value">${n.avgTime}s</div><div class="label">Avg</div></div>
        <div class="stat-item"><div class="value">${n.maxTime}s</div><div class="label">Max</div></div>
      </div></div>`;
  }
  document.getElementById('overview').innerHTML = html;
  document.getElementById('subtitle').textContent = `${m.logic} · ${m.totalFiles} files · ${m.date}`;
}

function makePieData(obj) {
  const keys = ['sat','unsat','unknown','timeout','error','killed'];
  return keys.map(k => ({label: LABELS[k], value: obj[k]||0, color: COLORS[k]})).filter(d => d.value > 0);
}

function renderPie(containerId, data, title) {
  const total = data.reduce((a,b)=>a+b.value,0);
  if (total === 0) { document.getElementById(containerId).innerHTML = `<div class="card chart-wrap"><h2>${title}</h2><div class="empty">No data</div></div>`; return; }
  let svg = `<svg width="200" height="200" viewBox="0 0 200 200"><g transform="translate(100,100)">`;
  let start = -Math.PI/2;
  data.forEach(d => {
    const angle = (d.value/total) * Math.PI*2;
    const x1 = Math.cos(start)*80, y1 = Math.sin(start)*80;
    const x2 = Math.cos(start+angle)*80, y2 = Math.sin(start+angle)*80;
    const large = angle > Math.PI ? 1 : 0;
    svg += `<path d="M 0 0 L ${x1} ${y1} A 80 80 0 ${large} 1 ${x2} ${y2} Z" fill="${d.color}" stroke="#fff" stroke-width="2"></path>`;
    // label line if slice big enough
    if (d.value/total > 0.08) {
      const mid = start + angle/2;
      const lx = Math.cos(mid)*55, ly = Math.sin(mid)*55;
      svg += `<text x="${lx}" y="${ly+4}" text-anchor="middle" fill="#fff" font-size="11" font-weight="600">${d.value}</text>`;
    }
    start += angle;
  });
  svg += `<circle r="45" fill="#fff"/></g></svg>`;
  let legend = `<div class="chart-legend">` + data.map(d => `<span><span class="legend-dot" style="background:${d.color}"></span>${d.label} ${d.value} (${(d.value/total*100).toFixed(1)}%)</span>`).join('') + `</div>`;
  document.getElementById(containerId).innerHTML = `<div class="card chart-wrap"><h2>${title}</h2>${svg}${legend}</div>`;
}

function renderCharts() {
  const container = document.getElementById('charts');
  container.innerHTML = `<div id="pie-nlc"></div><div id="pie-cmp"></div>`;
  renderPie('pie-nlc', makePieData(DATA.nlcolver), 'NLColver Results');
  if (DATA.compare) renderPie('pie-cmp', makePieData(DATA.compare), `${DATA.meta.compareWith} Results`);
  else document.getElementById('pie-cmp').innerHTML = '';
}

function renderMetrics() {
  const n = DATA.nlcolver;
  const c = DATA.compare;
  let html = `<div class="card"><h2>⏱ NLColver Timing</h2>`;
  html += `<div class="metric-row"><span>Total Time</span><strong>${n.totalTime}s</strong></div>`;
  html += `<div class="metric-row"><span>Average Time</span><strong>${n.avgTime}s</strong></div>`;
  html += `<div class="metric-row"><span>Max Time</span><strong>${n.maxTime}s</strong></div>`;
  html += `</div>`;
  if (c) {
    html += `<div class="card"><h2>⏱ ${DATA.meta.compareWith} Timing</h2>`;
    html += `<div class="metric-row"><span>Total Time</span><strong>${c.totalTime}s</strong></div>`;
    html += `<div class="metric-row"><span>Average Time</span><strong>${c.avgTime}s</strong></div>`;
    html += `<div class="metric-row"><span>Max Time</span><strong>${c.maxTime}s</strong></div>`;
    html += `</div>`;
  } else {
    html += `<div class="card"><h2>📁 Logic</h2><div class="metric-row"><span>Logic</span><strong>${DATA.meta.logic}</strong></div><div class="metric-row"><span>Wall-clock</span><strong>${DATA.meta.wallTime}s</strong></div><div class="metric-row"><span>Solver</span><strong>${DATA.meta.solver}</strong></div></div>`;
  }
  document.getElementById('metrics').innerHTML = html;
}

function renderTable() {
  const thead = document.getElementById('table-head');
  const hasCmp = DATA.meta.hasCompare;
  let h = `<th>File</th><th>NLColver</th><th>Time</th>`;
  if (hasCmp) h += `<th>${DATA.meta.compareWith}</th><th>Time</th><th>Match</th>`;
  thead.innerHTML = h;
  updateTable('all');
}

function rowHtml(r) {
  const hasCmp = DATA.meta.hasCompare;
  let s = `<td title="${r.file}">${r.file.length>90?r.file.slice(0,40)+'...'+r.file.slice(-45):r.file}</td>`;
  s += `<td>${badge(r.nlcolverResult, r.nlcolverResult)}</td>`;
  s += `<td>${r.nlcolverTime}s</td>`;
  if (hasCmp) {
    s += `<td>${badge(r.compareResult, r.compareResult)}</td>`;
    s += `<td>${r.compareTime}s</td>`;
    s += `<td>${badge(r.match.toLowerCase(), r.match)}</td>`;
  }
  return s;
}

function updateTable(filter, search='') {
  const tbody = document.getElementById('table-body');
  const rows = DATA.rows.filter(r => {
    if (search && !r.file.toLowerCase().includes(search.toLowerCase())) return false;
    if (filter === 'all') return true;
    if (filter === 'MATCH' || filter === 'MISMATCH' || filter === 'DIFF') return r.match === filter;
    return r.nlcolverResult === filter || r.compareResult === filter;
  });
  document.getElementById('table-count').textContent = `(${rows.length})`;
  if (rows.length === 0) { tbody.innerHTML = `<tr><td colspan="7" class="empty">No matching results</td></tr>`; return; }
  tbody.innerHTML = rows.map(r => `<tr>${rowHtml(r)}</tr>`).join('');
}

function renderAnomalies() {
  const container = document.getElementById('anomalies');
  const hasCmp = DATA.meta.hasCompare;
  let html = `<div class="section-title">⚠️ Anomalies</div><div class="grid cols-2">`;

  // Mismatches
  const mism = DATA.rows.filter(r => r.match === 'MISMATCH');
  html += `<div class="card"><h2>🔴 Mismatches (${mism.length})</h2>`;
  if (mism.length === 0) html += `<div class="empty">None</div>`;
  else mism.forEach(r => {
    html += `<div class="mismatch-card"><div class="title">${r.file}</div><div class="sub">NLColver: ${r.nlcolverResult} · ${DATA.meta.compareWith}: ${r.compareResult}</div></div>`;
  });
  html += `</div>`;

  // Timeouts / Errors for NLColver
  const nlcBad = DATA.rows.filter(r => r.nlcolverResult === 'timeout' || r.nlcolverResult === 'error' || r.nlcolverResult === 'killed');
  html += `<div class="card"><h2>🟠 NLColver Timeout / Error (${nlcBad.length})</h2>`;
  if (nlcBad.length === 0) html += `<div class="empty">None</div>`;
  else html += `<div class="scroll-table" style="max-height:300px"><table><thead><tr><th>File</th><th>Result</th><th>Time</th></tr></thead><tbody>`
    + nlcBad.slice(0,100).map(r => `<tr><td title="${r.file}">${r.file.length>60?r.file.slice(0,30)+'...'+r.file.slice(-25):r.file}</td><td>${badge(r.nlcolverResult, r.nlcolverResult)}</td><td>${r.nlcolverTime}s</td></tr>`).join('')
    + `</tbody></table></div>`;
  html += `</div>`;

  if (hasCmp) {
    const cmpBad = DATA.rows.filter(r => r.compareResult === 'timeout' || r.compareResult === 'error' || r.compareResult === 'killed');
    html += `<div class="card"><h2>🟠 ${DATA.meta.compareWith} Timeout / Error (${cmpBad.length})</h2>`;
    if (cmpBad.length === 0) html += `<div class="empty">None</div>`;
    else html += `<div class="scroll-table" style="max-height:300px"><table><thead><tr><th>File</th><th>Result</th><th>Time</th></tr></thead><tbody>`
      + cmpBad.slice(0,100).map(r => `<tr><td title="${r.file}">${r.file.length>60?r.file.slice(0,30)+'...'+r.file.slice(-25):r.file}</td><td>${badge(r.compareResult, r.compareResult)}</td><td>${r.compareTime}s</td></tr>`).join('')
      + `</tbody></table></div>`;
    html += `</div>`;

    const diffs = DATA.rows.filter(r => r.match === 'DIFF');
    html += `<div class="card"><h2>🟡 Diffs (${diffs.length})</h2>`;
    if (diffs.length === 0) html += `<div class="empty">None</div>`;
    else html += `<div class="scroll-table" style="max-height:300px"><table><thead><tr><th>File</th><th>NLColver</th><th>${DATA.meta.compareWith}</th><th>Note</th></tr></thead><tbody>`
      + diffs.slice(0,100).map(r => `<tr><td title="${r.file}">${r.file.length>50?r.file.slice(0,25)+'...'+r.file.slice(-20):r.file}</td><td>${badge(r.nlcolverResult, r.nlcolverResult)}</td><td>${badge(r.compareResult, r.compareResult)}</td><td>${r.note}</td></tr>`).join('')
      + `</tbody></table></div>`;
    html += `</div>`;
  }
  html += `</div>`;
  container.innerHTML = html;
}

function renderCategories() {
  const container = document.getElementById('categories');
  const cats = DATA.categoryStats;
  if (cats.length === 0) { container.innerHTML = ''; return; }
  let html = `<div class="section-title">📂 Category Statistics</div><div class="card"><div class="scroll-table"><table><thead><tr><th>Category</th><th>Count</th><th>NLColver SAT</th><th>NLColver UNSAT</th><th>NLColver T/O</th><th>NLColver Err</th>`;
  if (DATA.meta.hasCompare) html += `<th>${DATA.meta.compareWith} SAT</th><th>${DATA.meta.compareWith} UNSAT</th><th>${DATA.meta.compareWith} T/O</th><th>Mismatches</th>`;
  html += `</tr></thead><tbody>`;
  cats.forEach(c => {
    const n = c.nlcolver;
    html += `<tr><td><strong>${c.name}</strong></td><td>${c.count}</td>`;
    html += `<td style="color:${COLORS.sat}">${n.sat||0}</td><td style="color:${COLORS.unsat}">${n.unsat||0}</td><td style="color:${COLORS.timeout}">${n.timeout||0}</td><td style="color:${COLORS.error}">${n.error||0}</td>`;
    if (DATA.meta.hasCompare) {
      const cmp = c.compare||{};
      html += `<td style="color:${COLORS.sat}">${cmp.sat||0}</td><td style="color:${COLORS.unsat}">${cmp.unsat||0}</td><td style="color:${COLORS.timeout}">${cmp.timeout||0}</td>`;
      html += `<td>${c.mismatches>0?'<strong style="color:var(--c-mismatch)">'+c.mismatches+'</strong>':c.mismatches}</td>`;
    }
    html += `</tr>`;
  });
  html += `</tbody></table></div></div>`;
  container.innerHTML = html;
}

function renderTopSlow() {
  const container = document.getElementById('topslow');
  let html = `<div class="section-title">🐌 Top 50 Slowest</div><div class="grid cols-2">`;
  // NLColver
  html += `<div class="card"><h2>NLColver</h2><div class="scroll-table" style="max-height:400px"><table><thead><tr><th>#</th><th>Time</th><th>File</th></tr></thead><tbody>`;
  DATA.topSlowNlc.forEach((r,i) => {
    html += `<tr><td>${i+1}</td><td><strong>${r.time}s</strong></td><td title="${r.file}">${r.file.length>70?r.file.slice(0,35)+'...'+r.file.slice(-30):r.file}</td></tr>`;
  });
  html += `</tbody></table></div></div>`;
  // Compare
  if (DATA.meta.hasCompare) {
    html += `<div class="card"><h2>${DATA.meta.compareWith}</h2><div class="scroll-table" style="max-height:400px"><table><thead><tr><th>#</th><th>Time</th><th>File</th></tr></thead><tbody>`;
    DATA.topSlowCmp.forEach((r,i) => {
      html += `<tr><td>${i+1}</td><td><strong>${r.time}s</strong></td><td title="${r.file}">${r.file.length>70?r.file.slice(0,35)+'...'+r.file.slice(-30):r.file}</td></tr>`;
    });
    html += `</tbody></table></div></div>`;
  }
  html += `</div>`;
  container.innerHTML = html;
}

// Event wiring
document.querySelectorAll('.filter-bar button').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('.filter-bar button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    updateTable(btn.dataset.filter, document.getElementById('search').value);
  });
});
document.getElementById('search').addEventListener('input', e => {
  const filter = document.querySelector('.filter-bar button.active').dataset.filter;
  updateTable(filter, e.target.value);
});

// Init
renderOverview();
renderCharts();
renderMetrics();
renderTable();
renderAnomalies();
renderCategories();
renderTopSlow();
</script>
</body>
</html>'''



# =============================================================================
# Main
# =============================================================================

def run_single_logic(args, logic: str, output_dir: Path):
    """Run benchmark for a single logic and return statistics."""
    # Find files
    try:
        files = find_smt2_files(logic, filter_str=args.filter, max_files=args.max_files)
    except FileNotFoundError as e:
        print(f"ERROR: {e}")
        return None

    if not files:
        print(f"WARNING: No .smt2 files found for logic {logic}.")
        return None

    print(f"\n{'='*70}")
    print(f"Logic: {logic}")
    print(f"Files: {len(files)}")
    print(f"Jobs:  {args.jobs}")
    print(f"Timeout: {args.timeout}s")
    print(f"Solver: {args.solver}")
    if args.compare_with:
        print(f"Compare: {args.compare_with}")
    print("-" * 70)

    total = len(files)
    start_time = time.time()

    # -------------------------------------------------------------------------
    # Run NLColver
    # -------------------------------------------------------------------------
    nlcolver_results: List[RunResult] = []
    print(f"\n[1/2] Running NLColver on {total} files ...")

    if args.serial or args.jobs == 1:
        # True serial mode: no subprocess pool, lower memory footprint
        for i, f in enumerate(files, 1):
            res = run_nlcolver(f, args.solver, args.timeout, logic)
            nlcolver_results.append(res)
            if args.verbose or i % 100 == 0 or i == total:
                print(f"  NLColver: {i}/{total}  [{res.result:10s}] {res.file[:80]}")
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as executor:
            futures = {
                executor.submit(run_nlcolver, f, args.solver, args.timeout, logic): f
                for f in files
            }
            completed = 0
            for future in as_completed(futures):
                res = future.result()
                nlcolver_results.append(res)
                completed += 1
                if args.verbose or completed % 100 == 0 or completed == total:
                    print(f"  NLColver: {completed}/{total}  [{res.result:10s}] {res.file[:80]}")

    # -------------------------------------------------------------------------
    # Run comparison solver (if requested)
    # -------------------------------------------------------------------------
    compare_res_list: List[RunResult] = []
    if args.compare_with:
        print(f"\n[2/2] Running {args.compare_with} on {total} files ...")
        if args.serial or args.jobs == 1:
            for i, f in enumerate(files, 1):
                res = run_compare(f, args.compare_with, args.timeout)
                compare_res_list.append(res)
                if args.verbose or i % 100 == 0 or i == total:
                    print(f"  {args.compare_with}: {i}/{total}  [{res.result:10s}] {res.file[:80]}")
        else:
            with ProcessPoolExecutor(max_workers=args.jobs) as executor:
                futures = {
                    executor.submit(run_compare, f, args.compare_with, args.timeout): f
                    for f in files
                }
                completed = 0
                for future in as_completed(futures):
                    res = future.result()
                    compare_res_list.append(res)
                    completed += 1
                    if args.verbose or completed % 100 == 0 or completed == total:
                        print(f"  {args.compare_with}: {completed}/{total}  [{res.result:10s}] {res.file[:80]}")

    wall_time = time.time() - start_time
    print(f"\nAll done in {wall_time:.2f}s (wall-clock)")

    # -------------------------------------------------------------------------
    # Build comparison rows & statistics
    # -------------------------------------------------------------------------
    nlcolver_map = {r.file: r for r in nlcolver_results}
    compare_map = {r.file: r for r in compare_res_list}

    rows: List[ComparisonRow] = []
    stats = Statistics(logic=logic, total_files=total)

    for f in files:
        fstr = str(f)
        n = nlcolver_map[fstr]
        c = compare_map.get(fstr, RunResult(file=fstr, result="skip", elapsed=0.0, solver="none"))

        stats.nlcolver[n.result] += 1
        stats.total_time_nlcolver += n.elapsed
        stats.max_time_nlcolver = max(stats.max_time_nlcolver, n.elapsed)

        if args.compare_with:
            stats.compare[c.result] += 1
            stats.total_time_compare += c.elapsed
            stats.max_time_compare = max(stats.max_time_compare, c.elapsed)

            match, note = compare_results(n, c)
            if match == "MISMATCH":
                stats.mismatches += 1
            elif match == "DIFF":
                stats.diffs += 1
        else:
            match, note = "SKIP", ""

        # Category (subdirectory) stats
        rel = f.relative_to(BENCHMARK_ROOT / logic)
        cat = rel.parts[0] if rel.parts else "root"
        if cat not in stats.category_stats:
            stats.category_stats[cat] = {
                "count": 0,
                "nlcolver": defaultdict(int),
                "compare": defaultdict(int),
                "mismatches": 0,
                "diffs": 0,
            }
        stats.category_stats[cat]["count"] += 1
        stats.category_stats[cat]["nlcolver"][n.result] += 1
        if args.compare_with:
            stats.category_stats[cat]["compare"][c.result] += 1
            if match == "MISMATCH":
                stats.category_stats[cat]["mismatches"] += 1
            elif match == "DIFF":
                stats.category_stats[cat]["diffs"] += 1

        rows.append(ComparisonRow(
            file=fstr,
            nlcolver_result=n.result,
            nlcolver_time=n.elapsed,
            compare_result=c.result,
            compare_time=c.elapsed,
            match=match,
            note=note,
        ))

    if total > 0:
        stats.avg_time_nlcolver = stats.total_time_nlcolver / total
        if args.compare_with:
            stats.avg_time_compare = stats.total_time_compare / total

    # -------------------------------------------------------------------------
    # Generate reports
    # -------------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("Generating reports ...")
    print("=" * 70)

    write_summary(output_dir, stats, args, wall_time)
    write_csv(output_dir, rows)
    write_errors(output_dir, nlcolver_results, compare_res_list if args.compare_with else None)
    write_top_slow(output_dir, rows)
    if args.compare_with:
        write_discrepancies(output_dir, rows)
    write_json_stats(output_dir, stats, rows)
    write_html_report(output_dir, stats, rows, args, wall_time)

    # Category summary
    cat_path = output_dir / "category_summary.txt"
    with open(cat_path, "w") as f:
        f.write("=" * 70 + "\n")
        f.write("Per-Category Summary\n")
        f.write("=" * 70 + "\n\n")
        for cat, cstat in sorted(stats.category_stats.items()):
            f.write(f"[{cat}]  count={cstat['count']}\n")
            f.write(f"  nlcolver: {dict(cstat['nlcolver'])}\n")
            if args.compare_with:
                f.write(f"  compare:  {dict(cstat['compare'])}\n")
                f.write(f"  mismatches: {cstat['mismatches']}  diffs: {cstat['diffs']}\n")
            f.write("\n")
    print(f"[Category summary written to {cat_path}]")

    # Final console summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Logic:           {logic}")
    print(f"Files processed: {total}")
    print(f"Wall-clock time: {wall_time:.2f}s")
    print(f"NLColver:")
    for res in ["sat", "unsat", "unknown", "timeout", "error", "killed"]:
        cnt = stats.nlcolver.get(res, 0)
        print(f"  {res:12s}: {cnt:6d}")
    if args.compare_with:
        print(f"{args.compare_with}:")
        for res in ["sat", "unsat", "unknown", "timeout", "error", "killed"]:
            cnt = stats.compare.get(res, 0)
            print(f"  {res:12s}: {cnt:6d}")
        print(f"MISMATCHES:      {stats.mismatches} {'<<< CHECK!' if stats.mismatches > 0 else ''}")
        print(f"DIFFS:           {stats.diffs}")
    print(f"\nAll reports saved to: {output_dir}")
    print("=" * 70)

    return stats


def write_all_logics_summary(all_stats: List[Statistics], output_dir: Path, args):
    """Write a master summary for --all-logics run."""
    summary_path = output_dir / "all_logics_summary.txt"
    with open(summary_path, "w") as f:
        f.write("=" * 70 + "\n")
        f.write("NLColver All-Logics Benchmark Report\n")
        f.write("=" * 70 + "\n\n")
        f.write(f"Date:     {datetime.now().isoformat()}\n")
        f.write(f"Solver:   {args.solver}\n")
        f.write(f"Compare:  {args.compare_with or 'none'}\n")
        f.write(f"Timeout:  {args.timeout}s\n")
        f.write(f"Max files per logic: {args.max_files}\n")
        f.write("\n" + "-" * 70 + "\n")
        f.write(f"{'Logic':<15} {'Files':>6} {'sat':>6} {'unsat':>6} {'unk':>6} {'t/o':>6} {'err':>6} {'Mism':>6} {'Diff':>6}\n")
        f.write("-" * 70 + "\n")

        total_mismatches = 0
        total_diffs = 0
        for stats in all_stats:
            n = stats.nlcolver
            mism = stats.mismatches if args.compare_with else 0
            diff = stats.diffs if args.compare_with else 0
            total_mismatches += mism
            total_diffs += diff
            f.write(f"{stats.logic:<15} {stats.total_files:>6} "
                    f"{n.get('sat', 0):>6} {n.get('unsat', 0):>6} "
                    f"{n.get('unknown', 0):>6} {n.get('timeout', 0):>6} "
                    f"{n.get('error', 0):>6} {mism:>6} {diff:>6}\n")

        f.write("-" * 70 + "\n")
        f.write(f"{'TOTAL':<15} {sum(s.total_files for s in all_stats):>6} "
                f"{sum(s.nlcolver.get('sat', 0) for s in all_stats):>6} "
                f"{sum(s.nlcolver.get('unsat', 0) for s in all_stats):>6} "
                f"{sum(s.nlcolver.get('unknown', 0) for s in all_stats):>6} "
                f"{sum(s.nlcolver.get('timeout', 0) for s in all_stats):>6} "
                f"{sum(s.nlcolver.get('error', 0) for s in all_stats):>6} "
                f"{total_mismatches:>6} {total_diffs:>6}\n")
        f.write("\n")
        if total_mismatches > 0:
            f.write(f"*** WARNING: {total_mismatches} MISMATCH(es) detected! ***\n")
        f.write("=" * 70 + "\n")
    print(f"\n[All-logics summary written to {summary_path}]")
    return total_mismatches


def main():
    parser = argparse.ArgumentParser(
        description="NLColver Benchmark Runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python tools/run_benchmark.py --logic QF_LRA -j 8 -t 30
  python tools/run_benchmark.py --logic nia -j 4 -t 60 --compare-with z3
  python tools/run_benchmark.py --all-logics -j 8 -t 10 --compare-with z3 --max-files 50
  nohup python tools/run_benchmark.py --logic QF_NIA -j 8 -t 30 --compare-with z3 &
        """,
    )
    parser.add_argument("--logic", default=None, help="Logic to benchmark (e.g., QF_LRA, lra, nia)")
    parser.add_argument("--all-logics", action="store_true", help="Run on all available logics in benchmark dir")
    parser.add_argument("-j", "--jobs", type=int, default=1, help="Number of parallel jobs (default: 1)")
    parser.add_argument("-t", "--timeout", type=float, default=30, help="Timeout per instance in seconds (default: 30)")
    parser.add_argument("--solver", default=DEFAULT_SOLVER, help="Path to nlcolver binary")
    parser.add_argument("--compare-with", default=None, help="Path to comparison solver (e.g., z3, cvc5)")
    parser.add_argument("-o", "--output", default=None, help="Output directory (default: auto-generated)")
    parser.add_argument("--max-files", type=int, default=None, help="Limit number of files per logic (for quick tests)")
    parser.add_argument("--filter", default=None, help="Filter files by substring in relative path")
    parser.add_argument("--verbose", action="store_true", help="Verbose output")
    parser.add_argument("--serial", action="store_true", help="Run serially without subprocess pool (saves memory)")

    args = parser.parse_args()

    if not args.logic and not args.all_logics:
        parser.error("Either --logic or --all-logics must be specified.")

    # Validate solver binary
    if not os.path.isfile(args.solver):
        print(f"ERROR: NLColver binary not found: {args.solver}")
        sys.exit(1)

    if args.compare_with and not shutil.which(args.compare_with):
        print(f"ERROR: Comparison solver not found in PATH: {args.compare_with}")
        sys.exit(1)

    # Master output directory
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    master_dir = Path(args.output or f"benchmark_results/all_logics_{timestamp}")
    master_dir.mkdir(parents=True, exist_ok=True)

    if args.all_logics:
        logics = list_logic_dirs()
        if not logics:
            print("ERROR: No benchmark logic directories found.")
            sys.exit(1)
        print(f"Running on all {len(logics)} logics: {', '.join(logics)}")
        # Default max-files for --all-logics if not specified
        if args.max_files is None:
            args.max_files = 50
            print(f"Default --max-files set to {args.max_files} per logic (override with --max-files N)")
    else:
        try:
            logics = [resolve_logic(args.logic)]
        except ValueError as e:
            print(f"ERROR: {e}")
            sys.exit(1)

    all_stats = []
    for logic in logics:
        logic_dir = master_dir / logic
        logic_dir.mkdir(parents=True, exist_ok=True)
        stats = run_single_logic(args, logic, logic_dir)
        if stats:
            all_stats.append(stats)

    if args.all_logics and all_stats:
        total_mismatches = write_all_logics_summary(all_stats, master_dir, args)
        print(f"\n{'='*70}")
        print(f"ALL LOGICS COMPLETE: {len(all_stats)} logics, {sum(s.total_files for s in all_stats)} files")
        print(f"Master directory: {master_dir}")
        if args.compare_with:
            print(f"Total mismatches: {total_mismatches}")
        print(f"{'='*70}")
        if args.compare_with and total_mismatches > 0:
            sys.exit(2)


if __name__ == "__main__":
    main()
