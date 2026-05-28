"""eval.autotune — Z3-alpha-style staged offline autotuner over XOLVER_* flags.

Two stages, no re-solving between them:

  plan    : emit per-flag run commands for a small family-split train subset.
            baseline = floors only; then one run per candidate flag (floors +
            that flag). Run these on panda (heavy), pointing -o at a stage1 dir.

  combine : read the cached stage1 run dirs, score each, and select every flag
            that (a) improves solved AND (b) adds ZERO wrong vs baseline. Emit
            the per-logic best config (floors + selected flags). No re-solving.

The soundness floors are pinned ON in every candidate (see eval.flags), and any
flag that adds a wrong answer on train is rejected — so the search is aggressive
on completeness but cannot pick an unsound config. The final combined config is
still re-validated as a whole by eval.ci_gate before promotion.

Python 3.7+ / stdlib only.
"""
import argparse
import json
import os
import sys
from typing import Dict, List, Optional

from eval._compat import dataclass
from eval.flags import candidate_env, flags_for_logic
from eval.loader import load_run_dir
from eval.score import Score, score


# --------------------------------------------------------------------------- #
# Stage 2: combine cached per-flag scores into a selection
# --------------------------------------------------------------------------- #
@dataclass
class FlagEffect:
    flag: str
    baseline_solved: int
    flag_solved: int
    delta_solved: int
    added_wrong: int
    selected: bool
    reason: str


@dataclass
class CombineResult:
    selected_flags: List[str]
    effects: List[FlagEffect]


def combine(baseline: Score, per_flag: Dict[str, Score]) -> CombineResult:
    """Select flags that improve solved with zero added wrong (soundness gate)."""
    effects: List[FlagEffect] = []
    selected: List[str] = []
    for flag in sorted(per_flag):
        s = per_flag[flag]
        added_wrong = s.wrong - baseline.wrong
        delta = s.solved_1200 - baseline.solved_1200
        if added_wrong > 0:
            ok, reason = False, "rejected: +%d wrong (soundness)" % added_wrong
        elif delta > 0:
            ok, reason = True, "selected: +%d solved" % delta
        else:
            ok, reason = False, "no gain (delta=%d)" % delta
        effects.append(FlagEffect(flag, baseline.solved_1200, s.solved_1200,
                                  delta, added_wrong, ok, reason))
        if ok:
            selected.append(flag)
    return CombineResult(selected, effects)


# --------------------------------------------------------------------------- #
# Stage 1: emit per-flag run commands
# --------------------------------------------------------------------------- #
@dataclass
class RunSpec:
    label: str
    env: Dict[str, str]
    command: str


def make_run_command(env: Dict[str, str], solver: str, benchmark_dir: str, logic: str,
                     out_dir: str, timeout: float = 1200, jobs: int = 1,
                     compare_with: str = "z3", file_list: Optional[str] = None,
                     max_files: Optional[int] = None) -> str:
    """A single env-prefixed run_benchmark.py invocation (shell string)."""
    prefix = " ".join("%s=%s" % (k, v) for k, v in sorted(env.items()))
    parts = ["python3", "tools/run_benchmark.py",
             "--solver", solver, "--logic", logic, "--benchmark-dir", benchmark_dir,
             "--compare-with", compare_with, "-t", str(timeout), "-j", str(jobs),
             "-o", out_dir]
    if file_list:
        parts += ["--file-list", file_list]
    if max_files:
        parts += ["--max-files", str(max_files)]
    body = " ".join(parts)
    return ("%s %s" % (prefix, body)).strip()


def stage1_plan(logic: str, flags_to_test: List[str], solver: str, benchmark_dir: str,
                out_root: str, timeout: float = 1200, jobs: int = 1,
                compare_with: str = "z3", file_list: Optional[str] = None,
                max_files: Optional[int] = None) -> List[RunSpec]:
    """Baseline (floors only) + one run per candidate flag (floors + flag)."""
    specs: List[RunSpec] = []
    base_env = candidate_env([])
    specs.append(RunSpec("baseline", base_env,
                         make_run_command(base_env, solver, benchmark_dir, logic,
                                          os.path.join(out_root, "baseline"),
                                          timeout, jobs, compare_with, file_list, max_files)))
    for f in flags_to_test:
        env = candidate_env([f])
        specs.append(RunSpec(f, env,
                             make_run_command(env, solver, benchmark_dir, logic,
                                              os.path.join(out_root, f),
                                              timeout, jobs, compare_with, file_list, max_files)))
    return specs


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def _cmd_plan(args) -> int:
    flags_to_test = args.flags.split(",") if args.flags else flags_for_logic(args.logic)
    specs = stage1_plan(args.logic, flags_to_test, args.solver, args.benchmark_dir,
                        args.out_root, args.timeout, args.jobs, args.compare_with,
                        args.file_list, args.max_files)
    lines = ["#!/usr/bin/env bash",
             "# stage-1 autotune plan for %s (%d candidate flags). Run on panda."
             % (args.logic, len(flags_to_test)),
             "set -e"]
    for s in specs:
        lines.append("mkdir -p %s" % os.path.join(args.out_root, s.label))
        lines.append("echo '[stage1] %s'" % s.label)
        lines.append(s.command)
    text = "\n".join(lines) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        print("wrote stage-1 plan (%d runs) -> %s" % (len(specs), args.out))
    else:
        print(text)
    return 0


def _cmd_combine(args) -> int:
    base_dir = os.path.join(args.stage1_dir, "baseline")
    baseline = score(load_run_dir(base_dir), args.main_timeout, args.fast_timeout)
    per_flag: Dict[str, Score] = {}
    for name in sorted(os.listdir(args.stage1_dir)):
        sub = os.path.join(args.stage1_dir, name)
        if name == "baseline" or not os.path.isdir(sub):
            continue
        per_flag[name] = score(load_run_dir(sub), args.main_timeout, args.fast_timeout)
    res = combine(baseline, per_flag)
    print("baseline solved@1200=%d  wrong=%d" % (baseline.solved_1200, baseline.wrong))
    for e in res.effects:
        mark = "+" if e.selected else " "
        print("  [%s] %-32s %s" % (mark, e.flag, e.reason))
    print("\nSELECTED (%d): %s" % (len(res.selected_flags), ",".join(res.selected_flags)))
    env = candidate_env(res.selected_flags)
    if args.json:
        print(json.dumps({"logic": args.logic, "selected": res.selected_flags, "env": env}, indent=2))
    else:
        print("\n# per-logic config for %s (paste / source):" % args.logic)
        print("export " + " ".join("%s=%s" % (k, v) for k, v in sorted(env.items())))
    if args.out:
        with open(args.out, "w") as f:
            json.dump({"logic": args.logic, "selected": res.selected_flags, "env": env}, f, indent=2)
        print("wrote config -> %s" % args.out)
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Staged offline autotuner over XOLVER_* flags.")
    sub = p.add_subparsers(dest="cmd")
    sub.required = True  # set after creation: the required= kwarg is 3.7+ only

    pl = sub.add_parser("plan", help="emit stage-1 per-flag run commands")
    pl.add_argument("--logic", required=True)
    pl.add_argument("--solver", required=True)
    pl.add_argument("--benchmark-dir", required=True)
    pl.add_argument("--out-root", required=True, help="dir to hold per-flag run subdirs")
    pl.add_argument("--flags", default=None, help="comma-separated; default = flags_for_logic")
    pl.add_argument("--timeout", type=float, default=1200)
    pl.add_argument("--jobs", type=int, default=1)
    pl.add_argument("--compare-with", default="z3")
    pl.add_argument("--file-list", default=None, help="train-subset file list (family-split)")
    pl.add_argument("--max-files", type=int, default=None)
    pl.add_argument("--out", default=None, help="write the plan to a .sh file")
    pl.set_defaults(func=_cmd_plan)

    cb = sub.add_parser("combine", help="combine cached stage-1 runs into a config")
    cb.add_argument("--logic", required=True)
    cb.add_argument("--stage1-dir", required=True, help="dir with baseline/ + <FLAG>/ run subdirs")
    cb.add_argument("--main-timeout", type=float, default=1200)
    cb.add_argument("--fast-timeout", type=float, default=24)
    cb.add_argument("--json", action="store_true")
    cb.add_argument("--out", default=None, help="write the selected config JSON")
    cb.set_defaults(func=_cmd_combine)

    args = p.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
