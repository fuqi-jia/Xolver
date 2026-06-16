#!/usr/bin/env python3
"""
collect_features.py — build a (features -> winning config) training corpus for
learned per-instance strategy selection (#21) and autotuning (#22).

For each .smt2 in a tree it extracts the instance FEATURE VECTOR (via
`xolver solve <f> --features`, fast — no solve) and then solves it under each
named CONFIG (an env-flag set), recording the verdict + wall time. The emitted
JSONL (one row per instance×config) is the raw training data; a trivial
post-process picks, per instance, the config that solved it fastest = the label.

Pure data collection — never changes a verdict. SAFE ON WSL: every solve runs
under `ulimit -v` (default 4 GB) and the pool is capped (default -j2), because
heavy QF_NIA/QF_NRA cases can OOM the box.

Usage:
  python3 tools/collect_features.py --root <tree> --timeout 15 -j 2 \
          --out /tmp/corpus.jsonl
  # then label: per file, argmin(time) over rows with verdict in {sat,unsat}.

Configs default to baseline + the documented server-ready levers; override with
--configs name=ENV1=1,ENV2=1;name2=... (semicolon-separated, comma-separated env).
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

VERDICT_RE = re.compile(r"\b(unsat|sat|unknown)\b")

DEFAULT_CONFIGS = {
    "baseline": {},
    "nra_cuts": {"XOLVER_NRA_NLEXT_POWER": "1", "XOLVER_NRA_NLEXT_MONO_BOUND": "1",
                 "XOLVER_NRA_NLEXT_HIGHER": "1", "XOLVER_NRA_NLEXT_BERNSTEIN": "1",
                 "XOLVER_NRA_NLA_CUTS": "1"},
    "nia_linprop": {"XOLVER_NIA_LINEAR_PROP": "1"},
    "comb": {"XOLVER_EUF_PROP_COMB": "1", "XOLVER_AX_LAZY": "1"},
}


def run(argv, timeout, env=None, memkb=4194304):
    """Run with a hard memory cap (ulimit -v) so a blowup can't crash WSL."""
    full = ["bash", "-c",
            f'ulimit -v {memkb}; exec "$@"', "_"] + argv
    try:
        p = subprocess.run(full, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                           universal_newlines=True, timeout=timeout,
                           env={**os.environ, **(env or {})})
        return p.stdout or ""
    except subprocess.TimeoutExpired:
        return "__timeout__"
    except OSError:
        return "__error__"


def features(solver, f, timeout):
    out = run([str(solver), "solve", str(f), "--features"], timeout)
    line = next((l for l in out.splitlines() if l.startswith("{")), None)
    try:
        return json.loads(line) if line else {}
    except json.JSONDecodeError:
        return {}


def solve_one(solver, f, timeout, env):
    t0 = time.perf_counter()
    out = run([str(solver), "solve", str(f), "--timeout", str(int(timeout))],
              timeout + 5, env=env)
    dt = time.perf_counter() - t0
    m = VERDICT_RE.findall(out)
    verdict = m[-1] if m else ("timeout" if out == "__timeout__" else "error")
    return verdict, round(dt, 3)


def parse_configs(spec):
    if not spec:
        return DEFAULT_CONFIGS
    cfgs = {}
    for grp in spec.split(";"):
        if not grp.strip():
            continue
        name, _, envs = grp.partition("=")
        d = {}
        for kv in envs.split(","):
            k, _, v = kv.partition("=")
            if k:
                d[k.strip()] = (v.strip() or "1")
        cfgs[name.strip()] = d
    return cfgs


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", required=True, help="benchmark tree (recursive *.smt2)")
    ap.add_argument("--solver", default="build/bin/xolver")
    ap.add_argument("--timeout", type=float, default=15.0)
    ap.add_argument("-j", "--jobs", type=int, default=2, help="<=2 on WSL")
    ap.add_argument("--memkb", type=int, default=4194304, help="ulimit -v (KB), default 4G")
    ap.add_argument("--limit", type=int, default=0, help="sample at most N files")
    ap.add_argument("--configs", default="", help="name=ENV=1,...;name2=... (default: built-in set)")
    ap.add_argument("--out", default="/tmp/feature_corpus.jsonl")
    args = ap.parse_args()

    if args.jobs > 2:
        print("refusing -j>2 on WSL (memory safety); capping to 2", file=sys.stderr)
        args.jobs = 2

    files = sorted(Path(args.root).rglob("*.smt2"))
    if args.limit:
        files = files[: args.limit]
    if not files:
        print(f"no .smt2 under {args.root}", file=sys.stderr)
        return 2
    configs = parse_configs(args.configs)
    print(f"{len(files)} files x {len(configs)} configs "
          f"({', '.join(configs)}), timeout={args.timeout}s, -j{args.jobs}, "
          f"ulimit -v {args.memkb}KB")

    def work(f):
        feat = features(args.solver, f, args.timeout)
        rows = []
        for cname, env in configs.items():
            verdict, t = solve_one(args.solver, f, args.timeout,
                                   {**env, "XOLVER_WALLCLOCK_MS": str(int(args.timeout * 1000))})
            rows.append({"file": str(f), **feat, "config": cname,
                         "verdict": verdict, "time": t})
        return rows

    n = 0
    with open(args.out, "w") as out, ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for rows in ex.map(work, files):
            for r in rows:
                out.write(json.dumps(r) + "\n")
            n += 1
            if n % 100 == 0:
                print(f"  ... {n}/{len(files)}", file=sys.stderr)
    print(f"wrote {n} instances x {len(configs)} configs -> {args.out}")
    print("label per instance: argmin(time) over rows with verdict in {sat,unsat}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
