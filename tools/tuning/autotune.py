#!/usr/bin/env python3
"""#22 — continuous autotuning loop (gated default-flip proposer).

Automates the A/B-flag-flip process used to bake #41/#10/#16: for each candidate
gated flag, run the corpus with the flag OFF (baseline) then ON, measure the
solved / unsound / timeout deltas, and PROPOSE which flags are safe to promote to a
baked default. Soundness is the hard gate: any UNSOUND or UNEXPECTED_FAIL with a flag
ON => never bake, regardless of the solved-count delta.

Designed to be run on a schedule ("nightly"): point --root at the regression corpus
for a fast WSL sound-safety + neutrality gate, or at a benchmark subtree on a server
for the real net-win signal (the WSL regression corpus sits at the PASS ceiling, so
a true solved-count *increase* is only visible on the larger benchmark set).

Examples:
  # WSL sound-safety + neutrality gate over the regression corpus
  python3 tools/autotune.py --flags XOLVER_AX_LAZY XOLVER_NIA_NLA_CUTS
  # server net-win gate over a benchmark subtree, 2 repeats to damp timeout variance
  python3 tools/autotune.py --root benchmark/non-incremental/QF_NRA --repeat 2 \
      --flags XOLVER_NRA_GROBNER
"""
import argparse
import os
import re
import subprocess
import sys

_FIELDS = ("PASS", "UNSOUND", "UNEXPECTED_FAIL", "TIMEOUT", "KNOWN_FAIL")


def run_reg(solver, root, timeout, jobs, flag, value):
    """Run the regression harness once; return the summary counts."""
    env = dict(os.environ)
    if flag:
        env[flag] = value
    cmd = [sys.executable, "tools/regression/run_regression.py", "--root", root,
           "--solver", solver]
    out = subprocess.run(cmd, capture_output=True, text=True, env=env).stdout
    counts = {}
    for f in _FIELDS:
        m = re.search(rf"{f}\s*:\s*(\d+)", out)
        counts[f] = int(m.group(1)) if m else 0
    return counts


def best_of(solver, root, timeout, jobs, flag, value, repeat):
    """Run `repeat` times; keep the run with the most solved / fewest timeouts.

    Damps the parallel-regression timeout variance (a borderline case can tip past
    the per-case limit under -j contention without any real slowdown)."""
    runs = [run_reg(solver, root, timeout, jobs, flag, value) for _ in range(repeat)]
    # "best" = max PASS, then min TIMEOUT; UNSOUND is taken as the WORST seen (any
    # unsound in any repeat is disqualifying).
    best = max(runs, key=lambda c: (c["PASS"], -c["TIMEOUT"]))
    best = dict(best)
    best["UNSOUND"] = max(c["UNSOUND"] for c in runs)
    best["UNEXPECTED_FAIL"] = max(c["UNEXPECTED_FAIL"] for c in runs)
    return best


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver", default="build/bin/xolver")
    ap.add_argument("--root", default="tests/regression")
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--repeat", type=int, default=1,
                    help="runs per config; >1 damps timeout variance")
    ap.add_argument("--flags", nargs="+", required=True,
                    help="candidate gated flags to A/B and propose flips for")
    args = ap.parse_args()

    base = best_of(args.solver, args.root, args.timeout, args.jobs, None, None,
                   args.repeat)
    print(f"baseline (all flags default): {base}")
    proposals = []
    for flag in args.flags:
        on = best_of(args.solver, args.root, args.timeout, args.jobs, flag, "1",
                     args.repeat)
        d_pass = on["PASS"] - base["PASS"]
        d_to = on["TIMEOUT"] - base["TIMEOUT"]
        sound = on["UNSOUND"] == 0 and on["UNEXPECTED_FAIL"] == 0
        # Promote only if sound AND (net solved-count non-decreasing) AND not adding
        # timeouts. A strict net WIN (d_pass > 0) is what justifies a competition bake;
        # d_pass == 0 with a known out-of-corpus benefit is a "neutral — needs bench".
        if not sound:
            verdict = "REJECT (UNSOUND — never bake)"
        elif d_pass > 0 and d_to <= 0:
            verdict = "BAKE (net win)"
        elif d_pass == 0 and d_to <= 0:
            verdict = "NEUTRAL in-corpus (needs benchmark for net-win signal)"
        else:
            verdict = "HOLD (regression: fewer solved or more timeouts)"
        print(f"  {flag}=1: {on}  dPASS={d_pass:+d} dTIMEOUT={d_to:+d}  -> {verdict}")
        proposals.append((flag, verdict))

    bake = [f for f, v in proposals if v.startswith("BAKE")]
    if bake:
        print("\nPROPOSED for kFlags[] (tools/cli/main.cpp): " + " ".join(bake))
    else:
        print("\nNo flag proposed for an in-corpus bake (sound-safe flips with an "
              "out-of-corpus benefit still need a benchmark net-win run).")


if __name__ == "__main__":
    main()
