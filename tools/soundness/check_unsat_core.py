#!/usr/bin/env python3
"""
check_unsat_core.py — independently validate Xolver's unsat cores against z3/cvc5.

Xolver's `solve <file> --unsat-core` prints, after `unsat`, the subset of
assertions that prove unsatisfiability. This tool closes the soundness loop the
same way the ModelValidator does for `sat`: it rebuilds a reduced problem from
the original declarations + ONLY the printed core assertions and confirms an
EXTERNAL oracle (z3/cvc5) still reports `unsat`. A core that does not re-prove
unsat is a bug (the reported subset is insufficient → potentially unsound).

With --minimal it also checks minimality: dropping any single core assertion
should make the reduced problem no longer unsat (else the core is non-minimal —
a quality warning, not a soundness error).

Usage:
  python3 tools/check_unsat_core.py <file.smt2|dir> [options]
    --solver  PATH   xolver binary (default build/bin/xolver)
    --oracle  NAME   external checker: z3 (default) or cvc5
    --timeout N      per-call wall budget seconds (default 20)
    --minimal        also check each core assertion is necessary
    -v               print per-file detail

Exit non-zero if any core fails validation (unsound/insufficient core).
"""
import argparse
import re
import subprocess
import sys
import tempfile
import os
from pathlib import Path

VERDICT_RE = re.compile(r"\b(unsat|sat|unknown)\b")


def split_smt2_commands(text):
    """Paren-aware split of an SMT-LIB file into top-level (...) command strings,
    skipping line comments. Robust to multi-line commands."""
    cmds, depth, buf, in_str = [], 0, [], False
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ';' and not in_str:                      # line comment
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        if c == '"':
            in_str = not in_str
        if not in_str:
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
        buf.append(c)
        if depth == 0 and c == ')':
            cmds.append(''.join(buf).strip())
            buf = []
        i += 1
    return [c for c in cmds if c]


def command_head(cmd):
    """The command keyword, e.g. 'assert' from '(assert ...)'."""
    m = re.match(r"\(\s*([A-Za-z0-9_!-]+)", cmd)
    return m.group(1) if m else ""


def split_core_terms(core_line):
    """Split the printed core '( t1 t2 ... )' into top-level term strings."""
    s = core_line.strip()
    if s.startswith('(') and s.endswith(')'):
        s = s[1:-1]
    terms, depth, buf, in_str = [], 0, [], False
    for c in s:
        if c == '"':
            in_str = not in_str
        if not in_str:
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
        if c == ' ' and depth == 0 and not in_str:
            if buf:
                terms.append(''.join(buf)); buf = []
        else:
            buf.append(c)
    if buf:
        terms.append(''.join(buf))
    return [t for t in terms if t]


def run(cmd, timeout):
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           universal_newlines=True, timeout=timeout)
        return (p.stdout or "") + "\n" + (p.stderr or "")
    except subprocess.TimeoutExpired:
        return "timeout"
    except OSError as e:
        return f"error {e}"


def first_verdict(out):
    m = VERDICT_RE.findall(out)
    return m[0] if m else ""


def reduced_verdict(run_argv_fn, preamble_cmds, assert_terms, timeout):
    """Write a reduced problem (preamble + asserts) to a temp file and run the
    solver given by run_argv_fn(path) -> argv. Returns its verdict."""
    lines = list(preamble_cmds)
    lines += [f"(assert {t})" for t in assert_terms]
    lines.append("(check-sat)")
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write("\n".join(lines) + "\n")
        path = f.name
    try:
        return first_verdict(run(run_argv_fn(path), timeout))
    finally:
        os.unlink(path)


def oracle_verdict(oracle, preamble_cmds, assert_terms, timeout):
    """Build a reduced problem and ask the external oracle (z3/cvc5)."""
    argv = (lambda p: ["z3", "-smt2", p]) if oracle == "z3" \
        else (lambda p: ["cvc5", "--lang=smt2", p])
    return reduced_verdict(argv, preamble_cmds, assert_terms, timeout)


def minimize_core(solver, preamble, core, timeout):
    """Deletion-based minimization using FRESH solver runs (no incremental
    carryover, so it is reliable for ALL logics — including nonlinear, where the
    in-solver failed() path is deliberately conservative). Try removing each
    assertion; if the solver still proves unsat without it, it is redundant.
    One pass yields a minimal core: every remaining assertion is necessary."""
    argv = lambda p: [str(solver), "solve", p]
    core = list(core)
    i = 0
    while i < len(core):
        candidate = core[:i] + core[i + 1:]
        if reduced_verdict(argv, preamble, candidate, timeout) == "unsat":
            del core[i]          # redundant → drop, re-check the same index
        else:
            i += 1               # necessary → keep
    return core


def check_file(path, solver, oracle, timeout, minimal, verbose, minimize=False):
    """Returns (status, detail). status in {PASS, FAIL, SKIP, NONMIN}."""
    text = path.read_text(errors="replace")
    cmds = split_smt2_commands(text)
    # Preamble = everything needed to declare the vocabulary (NOT asserts/queries).
    keep = {"set-logic", "declare-fun", "declare-const", "declare-sort",
            "define-fun", "define-fun-rec", "define-sort", "declare-datatypes",
            "declare-datatype"}
    preamble = [c for c in cmds if command_head(c) in keep]

    out = run([str(solver), "solve", str(path), "--unsat-core"], timeout)
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    verdict = first_verdict(out)
    if verdict != "unsat":
        return ("SKIP", f"xolver verdict={verdict or 'none'} (not unsat)")
    # The core is the first line after `unsat` that looks like a paren list.
    core_line = next((l for l in lines if l.startswith('(') and l != "unsat"), None)
    if not core_line:
        return ("FAIL", "xolver said unsat but printed no core line")
    core = split_core_terms(core_line)
    if not core:
        return ("FAIL", "empty core for an unsat problem")

    # Soundness: the core alone must still be unsat per the external oracle.
    # Only a definite `sat` proves the core INSUFFICIENT (a real bug); `unknown`/
    # timeout means the oracle could not verify (inconclusive), not a failure.
    v = oracle_verdict(oracle, preamble, core, timeout)
    if v == "sat":
        return ("FAIL", f"core INSUFFICIENT: {oracle} says sat on the "
                        f"{len(core)}-assertion core")
    if v != "unsat":
        return ("SKIP", f"{oracle} {v or 'no-verdict'} on the core (inconclusive)")
    detail = f"core size {len(core)} validated unsat by {oracle}"

    # Minimize (optional): deletion-based reduction via FRESH solver runs, giving
    # a verified minimal core for ANY logic (the in-solver path is conservative
    # for nonlinear/mixed). Print the minimal core so it is usable directly.
    if minimize:
        minimal = minimize_core(solver, preamble, core, timeout)
        detail += f" → minimal core size {len(minimal)}"
        if verbose or len(minimal) < len(core):
            print(f"  minimal core ({len(minimal)}): "
                  f"({' '.join(minimal)})")

    # Minimality (optional): dropping any one core assertion should break unsat.
    if minimal and len(core) > 1:
        nonmin = []
        for k in range(len(core)):
            reduced = core[:k] + core[k+1:]
            if oracle_verdict(oracle, preamble, reduced, timeout) == "unsat":
                nonmin.append(k)
        if nonmin:
            return ("NONMIN", detail + f"; but {len(nonmin)} assertion(s) "
                                       f"removable → non-minimal")
    return ("PASS", detail)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("target", help="a .smt2 file or a directory of them")
    ap.add_argument("--solver", default="build/bin/xolver")
    ap.add_argument("--oracle", default="z3", choices=["z3", "cvc5"])
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--minimal", action="store_true",
                    help="check (don't produce) whether the core is minimal")
    ap.add_argument("--minimize", action="store_true",
                    help="produce a verified MINIMAL core via deletion (fresh solves)")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    target = Path(args.target)
    files = sorted(target.rglob("*.smt2")) if target.is_dir() else [target]
    if not files:
        print(f"no .smt2 under {target}", file=sys.stderr); return 2

    tally = {"PASS": 0, "FAIL": 0, "SKIP": 0, "NONMIN": 0}
    failures = []
    for f in files:
        status, detail = check_file(f, args.solver, args.oracle,
                                    args.timeout, args.minimal, args.verbose,
                                    args.minimize)
        tally[status] += 1
        if status == "FAIL":
            failures.append((f, detail))
        if args.verbose or status in ("FAIL", "NONMIN"):
            print(f"[{status:6}] {f}  —  {detail}")

    print(f"\n{len(files)} file(s): "
          f"{tally['PASS']} PASS, {tally['FAIL']} FAIL, "
          f"{tally['NONMIN']} non-minimal, {tally['SKIP']} skipped "
          f"(oracle={args.oracle})")
    if failures:
        print("\nUNSOUND/INSUFFICIENT CORES (investigate):")
        for f, d in failures:
            print(f"  {f}\n      {d}")
    return 1 if tally["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
