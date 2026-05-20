#!/usr/bin/env python3
"""
NLColver Benchmark Server Orchestrator

Compiles solver, runs benchmark, analyzes results, and commits compact
artifacts to a dedicated git worktree.

Usage:
    # Smoke test (deterministic, fast)
    python tools/bench_server.py --mode smoke --timeout 10 --jobs 32 --git-push

    # Focus on one logic
    python tools/bench_server.py --mode focus --focus-logic QF_LRA --timeout 30 --jobs 32 --git-push

    # Full benchmark
    python tools/bench_server.py --mode full --timeout 10 --jobs 32 \
        --baseline-raw-run /data/bench-runs/2026-05-19_2100_nlcolver_def4567 \
        --compare-with-z3-baseline /data/bench-baselines/z3_4.12.2_xxx_t10.json \
        --git-worktree ../repo-bench-results --git-push
"""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

BENCHMARK_ROOT = Path("benchmark/non-incremental")
DEFAULT_SOLVER = "./build/bin/nlcolver"
SERVER_LOCAL_DIR = Path("/data/bench-runs")  # server-side raw storage


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def run(cmd, cwd=None, check=True, capture=True):
    """Run a shell command."""
    print(f"[RUN] {' '.join(cmd) if isinstance(cmd, list) else cmd}")
    kwargs = {"cwd": cwd, "check": check}
    if capture:
        kwargs["capture_output"] = True
        kwargs["text"] = True
    return subprocess.run(cmd, **kwargs)


def git_commit_hash():
    r = run(["git", "rev-parse", "HEAD"], check=False)
    return r.stdout.strip() if r.returncode == 0 else "unknown"


def git_is_clean():
    r = run(["git", "status", "--porcelain"], check=False)
    return r.returncode == 0 and not r.stdout.strip()


def ensure_git_worktree(worktree_path: Path, branch: str):
    """Ensure a git worktree exists for bench-results."""
    if not (worktree_path / ".git").exists():
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        run(["git", "worktree", "add", str(worktree_path), branch], check=False)
    # If worktree exists but branch doesn't, create orphan branch
    if not (worktree_path / ".git").exists():
        run(["git", "worktree", "add", "--orphan", str(worktree_path), branch], check=False)


# ---------------------------------------------------------------------------
# Main flow
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="NLColver Benchmark Server")
    parser.add_argument("--mode", choices=["smoke", "focus", "full"], required=True)
    parser.add_argument("--focus-logic", default=None, help="Logic for focus mode")
    parser.add_argument("--smoke-manifest", default="tools/smoke_manifest.txt",
                        help="Fixed manifest for smoke mode")
    parser.add_argument("-t", "--timeout", type=float, default=30)
    parser.add_argument("-j", "--jobs", type=int, default=1)
    parser.add_argument("--solver", default=DEFAULT_SOLVER)
    parser.add_argument("--baseline-raw-run", default=None,
                        help="Path to baseline raw run directory (server local)")
    parser.add_argument("--compare-with-z3-baseline", default=None,
                        help="Path to Z3 frozen baseline JSON (server local)")
    parser.add_argument("--git-worktree", default="../repo-bench-results",
                        help="Path to git worktree for bench-results")
    parser.add_argument("--git-branch", default="bench-results")
    parser.add_argument("--git-push", action="store_true", default=True,
                        help="Push results to remote (default: True)")
    parser.add_argument("--no-push", action="store_true",
                        help="Skip git push")
    parser.add_argument("--output-prefix", default="bench_results",
                        help="Prefix for run ID")
    parser.add_argument("--keep-last", type=int, default=20,
                        help="Number of runs to keep in result branch")
    args = parser.parse_args()

    if args.no_push:
        args.git_push = False

    # Validate
    if not Path(args.solver).exists():
        print(f"ERROR: Solver not found: {args.solver}")
        sys.exit(1)

    commit = git_commit_hash()
    print(f"[INFO] Commit: {commit}")
    if not git_is_clean():
        print("[WARNING] Working directory is not clean. Continue anyway.")

    # Build solver
    print("[INFO] Building solver...")
    build_dir = Path("build")
    if not (build_dir / "CMakeCache.txt").exists():
        run(["cmake", "-DNLCOLVER_ENABLE_CASESTATS=ON", ".."], cwd=build_dir)
    run(["cmake", "--build", ".", "-j", str(args.jobs)], cwd=build_dir)

    # Prepare run directories
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_id = f"{timestamp}_{args.output_prefix}_{commit[:7]}"
    server_run_dir = SERVER_LOCAL_DIR / run_id
    server_run_dir.mkdir(parents=True, exist_ok=True)

    raw_stats_dir = server_run_dir / "raw_stats"
    raw_stats_dir.mkdir(exist_ok=True)
    log_dir = server_run_dir / "logs"
    log_dir.mkdir(exist_ok=True)

    # Prepare run_benchmark.py args
    bench_args = [
        sys.executable, "tools/run_benchmark.py",
        "--solver", args.solver,
        "-j", str(args.jobs),
        "-t", str(args.timeout),
        "--dump-stats-dir", str(raw_stats_dir),
        "--log-dir", str(log_dir),
        "--manifest-out", str(server_run_dir / "manifest.txt"),
    ]

    if args.mode == "smoke":
        # Read smoke manifest and run each logic
        smoke_files = []
        with open(args.smoke_manifest) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    smoke_files.append(line)
        # Write temporary file list and pass to runner
        smoke_list = server_run_dir / "smoke_files.txt"
        with open(smoke_list, "w") as f:
            for line in smoke_files:
                f.write(line + "\n")
        bench_args += ["--file-list", str(smoke_list)]
    elif args.mode == "focus":
        if not args.focus_logic:
            print("ERROR: --focus-logic required for focus mode")
            sys.exit(1)
        bench_args += ["--logic", args.focus_logic]
    else:  # full
        bench_args += ["--all-logics"]

    # Record meta start
    meta = {
        "run_id": run_id,
        "commit": commit,
        "branch": "main",
        "build_type": "Release",
        "timeout_sec": args.timeout,
        "jobs": args.jobs,
        "mode": args.mode,
        "start_time": datetime.now().isoformat(),
    }

    # Run benchmark
    print(f"[INFO] Running benchmark: {run_id}")
    bench_start = time.time()
    try:
        run(bench_args, check=True)
        meta["bench_exit_code"] = 0
    except subprocess.CalledProcessError as e:
        print(f"[WARNING] Benchmark runner exited with code {e.returncode}")
        meta["bench_exit_code"] = e.returncode

    bench_wall = time.time() - bench_start
    meta["bench_wall_sec"] = bench_wall

    # Generate manifest hash
    manifest_path = server_run_dir / "manifest.txt"
    if manifest_path.exists():
        with open(manifest_path, "rb") as f:
            meta["manifest_hash"] = "sha256:" + hashlib.sha256(f.read()).hexdigest()

    # Run analyzer
    analyze_args = [
        sys.executable, "tools/analyze_benchmark.py",
        "--current", str(server_run_dir),
        "--output", str(server_run_dir / "analysis"),
        "--run-id", run_id,
        "--commit", commit,
        "--timeout", str(args.timeout),
    ]
    if args.baseline_raw_run:
        analyze_args += ["--baseline", args.baseline_raw_run]
        analyze_args += ["--baseline-run-id", Path(args.baseline_raw_run).name]
    if args.compare_with_z3_baseline:
        analyze_args += ["--z3-baseline", args.compare_with_z3_baseline]

    print("[INFO] Running analyzer...")
    try:
        run(analyze_args, check=True)
    except subprocess.CalledProcessError as e:
        print(f"[WARNING] Analyzer exited with code {e.returncode}")

    # Record end time
    meta["end_time"] = datetime.now().isoformat()
    meta["total_wall_sec"] = time.time() - bench_start
    with open(server_run_dir / "analysis" / "meta.json", "w") as f:
        json.dump(meta, f, indent=2)

    # Copy to git worktree
    worktree = Path(args.git_worktree).resolve()
    ensure_git_worktree(worktree, args.git_branch)

    target_run_dir = worktree / "runs" / run_id
    target_run_dir.mkdir(parents=True, exist_ok=True)

    analysis_dir = server_run_dir / "analysis"
    for f in analysis_dir.iterdir():
        if f.is_file():
            shutil.copy2(f, target_run_dir / f.name)

    # Copy latest.md
    summary_src = analysis_dir / "summary.md"
    if summary_src.exists():
        shutil.copy2(summary_src, worktree / "latest.md")

    # Git commit
    print("[INFO] Committing to bench-results branch...")
    run(["git", "add", "latest.md", f"runs/{run_id}/"], cwd=worktree)
    run(["git", "commit", "-m", f"bench: {run_id}"], cwd=worktree, check=False)

    if args.git_push:
        run(["git", "push", "origin", args.git_branch], cwd=worktree, check=False)
        print("[INFO] Pushed to remote.")
    else:
        print("[INFO] Skipped push (--no-push).")

    # Cleanup old runs (append-only: only remove from checkout, not history)
    if args.keep_last > 0:
        runs_dir = worktree / "runs"
        if runs_dir.exists():
            all_runs = sorted(runs_dir.iterdir(), key=lambda p: p.stat().st_mtime)
            if len(all_runs) > args.keep_last:
                for old in all_runs[:-args.keep_last]:
                    print(f"[INFO] Removing old run from checkout: {old.name}")
                    shutil.rmtree(old)
                run(["git", "add", "runs/"], cwd=worktree, check=False)
                run(["git", "commit", "-m", f"bench: cleanup old runs (keep {args.keep_last})"],
                    cwd=worktree, check=False)
                if args.git_push:
                    run(["git", "push", "origin", args.git_branch], cwd=worktree, check=False)

    print(f"[DONE] Run {run_id} complete. Analysis at {target_run_dir}")


if __name__ == "__main__":
    main()
