#!/usr/bin/env python3
"""Differential soundness fuzzer for Xolver combination logics.

Generates small, well-typed QF_AUFLIA / QF_ALIA / QF_UFLIA formulas exercising the
Nelson-Oppen combination surface (arrays + UF over LIA), runs xolver vs z3 AND cvc5,
and flags:
  * UNSOUND  : xolver and BOTH oracles in {sat,unsat} but xolver disagrees (release blocker)
  * GAP      : xolver=unknown where z3 and cvc5 agree on a definite verdict
Deterministic (seeded). WSL-friendly: small formulas, short timeouts.

Usage: python3 tools/fuzz_combination_soundness.py [--n N] [--seed S] [--solver PATH]
"""
import argparse, random, subprocess, sys, tempfile, os

def run(cmd, inp, timeout):
    try:
        p = subprocess.run(cmd, input=inp, capture_output=True, text=True, timeout=timeout)
        out = (p.stdout + " " + p.stderr).strip().lower()
    except subprocess.TimeoutExpired:
        return "timeout"
    except Exception:
        return "error"
    # first verdict token
    for tok in out.split():
        if tok in ("sat", "unsat", "unknown"):
            return tok
    if "error" in out or "unexpected" in out or "unsupported" in out:
        return "error"
    return "unknown"

class Gen:
    def __init__(self, rng, logic):
        self.rng = rng
        self.logic = logic
        body = logic.replace("QF_", "")
        self.is_real = "LRA" in body
        self.has_array = body.startswith("A") or "AUF" in body
        self.has_uf = "UF" in body
        self.esort = "Real" if self.is_real else "Int"
        self.int_vars = ["i", "j", "k"]
        self.arr_vars = ["a", "b", "c"] if self.has_array else []
        # value tokens are well-typed for the element sort
        self.consts = (["0.0", "1.0", "2.0", "(- 1.0)", "5.0"] if self.is_real
                       else ["0", "1", "2", "(- 1)", "5"])

    def int_term(self, d):
        r = self.rng
        choices = ["var", "const"]
        if d > 0:
            choices += ["add", "sub"]
            if self.arr_vars: choices += ["select"]
            if self.has_uf: choices += ["uf_int", "uf_arr"] if self.arr_vars else ["uf_int"]
        c = r.choice(choices)
        if c == "var": return r.choice(self.int_vars)
        if c == "const": return r.choice(self.consts)
        if c == "add": return f"(+ {self.int_term(d-1)} {self.int_term(d-1)})"
        if c == "sub": return f"(- {self.int_term(d-1)} {self.int_term(d-1)})"
        if c == "select": return f"(select {self.arr_term(d-1)} {self.int_term(d-1)})"
        if c == "uf_int": return f"(f {self.int_term(d-1)})"
        if c == "uf_arr": return f"(g {self.arr_term(d-1)})"
        return "0"

    def arr_term(self, d):
        r = self.rng
        if d <= 0 or not self.arr_vars or r.random() < 0.5:
            return r.choice(self.arr_vars)
        return f"(store {self.arr_term(d-1)} {self.int_term(d-1)} {self.int_term(d-1)})"

    def atom(self, d):
        r = self.rng
        kinds = ["int_eq", "int_le", "int_lt", "int_neq"]
        if self.arr_vars: kinds += ["arr_eq", "arr_neq"]
        if self.has_uf and self.arr_vars: kinds += ["bool_uf_eq"]
        k = r.choice(kinds)
        if k == "int_eq": return f"(= {self.int_term(d)} {self.int_term(d)})"
        if k == "int_le": return f"(<= {self.int_term(d)} {self.int_term(d)})"
        if k == "int_lt": return f"(< {self.int_term(d)} {self.int_term(d)})"
        if k == "int_neq": return f"(distinct {self.int_term(d)} {self.int_term(d)})"
        if k == "arr_eq": return f"(= {self.arr_term(d)} {self.arr_term(d)})"
        if k == "arr_neq": return f"(distinct {self.arr_term(d)} {self.arr_term(d)})"
        if k == "bool_uf_eq": return f"(= (h {self.arr_term(d)}) (h {self.arr_term(d)}))"
        return "true"

    def formula(self):
        r = self.rng
        es = self.esort
        arr = f"(Array {es} {es})"   # uniform index/element sort keeps gen well-typed
        lines = [f"(set-logic {self.logic})"]
        for v in self.int_vars: lines.append(f"(declare-fun {v} () {es})")
        for v in self.arr_vars: lines.append(f"(declare-fun {v} () {arr})")
        if self.has_uf:
            lines.append(f"(declare-fun f ({es}) {es})")
            if self.arr_vars:
                lines.append(f"(declare-fun g ({arr}) {es})")
                lines.append(f"(declare-fun h ({arr}) Bool)")
        n = r.randint(2, 7)
        for _ in range(n):
            a = self.atom(r.randint(1, 3))
            if r.random() < 0.3: a = f"(not {a})"
            lines.append(f"(assert {a})")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"

class DtGen:
    """QF_UFDTLIA: a Pair datatype over Int + UF, exercising constructor/selector/
    tester congruence in combination (validates the #66 datatype routing at scale)."""
    def __init__(self, rng):
        self.rng = rng
        self.logic = "QF_UFDTLIA"
        self.int_vars = ["i", "j", "k"]
        self.pair_vars = ["p", "q", "r"]
        self.iconsts = ["0", "1", "2", "(- 1)", "5"]

    def int_term(self, d):
        r = self.rng
        ch = ["var", "const"]
        if d > 0: ch += ["add", "sub", "fst", "snd", "uf"]
        c = r.choice(ch)
        if c == "var": return r.choice(self.int_vars)
        if c == "const": return r.choice(self.iconsts)
        if c == "add": return f"(+ {self.int_term(d-1)} {self.int_term(d-1)})"
        if c == "sub": return f"(- {self.int_term(d-1)} {self.int_term(d-1)})"
        if c == "fst": return f"(fst {self.pair_term(d-1)})"
        if c == "snd": return f"(snd {self.pair_term(d-1)})"
        if c == "uf":  return f"(f {self.pair_term(d-1)})"
        return "0"

    def pair_term(self, d):
        r = self.rng
        if d <= 0 or r.random() < 0.5: return r.choice(self.pair_vars)
        return f"(mk {self.int_term(d-1)} {self.int_term(d-1)})"

    def atom(self, d):
        r = self.rng
        k = r.choice(["int_eq", "int_le", "pair_eq", "pair_neq", "tester"])
        if k == "int_eq":  return f"(= {self.int_term(d)} {self.int_term(d)})"
        if k == "int_le":  return f"(<= {self.int_term(d)} {self.int_term(d)})"
        if k == "pair_eq": return f"(= {self.pair_term(d)} {self.pair_term(d)})"
        if k == "pair_neq":return f"(distinct {self.pair_term(d)} {self.pair_term(d)})"
        if k == "tester":  return f"((_ is mk) {self.pair_term(d)})"
        return "true"

    def formula(self):
        r = self.rng
        lines = [f"(set-logic {self.logic})",
                 "(declare-datatype Pair ((mk (fst Int) (snd Int))))"]
        for v in self.int_vars: lines.append(f"(declare-fun {v} () Int)")
        for v in self.pair_vars: lines.append(f"(declare-fun {v} () Pair)")
        lines.append("(declare-fun f (Pair) Int)")
        for _ in range(r.randint(2, 7)):
            a = self.atom(r.randint(1, 3))
            if r.random() < 0.3: a = f"(not {a})"
            lines.append(f"(assert {a})")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=400)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--solver", default="build/bin/xolver")
    ap.add_argument("--timeout", type=float, default=6.0)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    logics = ["QF_AUFLIA", "QF_ALIA", "QF_UFLIA",
              "QF_AUFLRA", "QF_ALRA", "QF_UFLRA", "QF_UFDTLIA"]
    unsound, gaps, checked = [], [], 0
    tmpf = os.path.join(tempfile.gettempdir(), f"fuzz_{os.getpid()}.smt2")
    for idx in range(args.n):
        logic = rng.choice(logics)
        smt = (DtGen(rng) if logic == "QF_UFDTLIA" else Gen(rng, logic)).formula()
        with open(tmpf, "w") as fh:
            fh.write(smt)
        xo = run([args.solver, "solve", tmpf], "", args.timeout)
        if xo not in ("sat", "unsat", "unknown"):
            continue
        z3 = run(["z3", "-in"], smt, args.timeout)
        cv = run(["cvc5", "--lang", "smt2"], smt, args.timeout)
        defs = {"sat", "unsat"}
        if z3 in defs and cv in defs and z3 == cv:
            checked += 1
            if xo in defs and xo != z3:
                unsound.append((smt, xo, z3, cv))
                print(f"\n!!!!! UNSOUND #{idx} ({logic}): xolver={xo} z3={z3} cvc5={cv}\n{smt}")
            elif xo == "unknown":
                gaps.append((smt, xo, z3, cv))
        if idx % 50 == 0:
            print(f"[{idx}/{args.n}] checked={checked} unsound={len(unsound)} gaps={len(gaps)}", file=sys.stderr)
    print(f"\n==== DONE: generated={args.n} oracle-agreed={checked} "
          f"UNSOUND={len(unsound)} GAPS={len(gaps)} ====")
    if gaps and not unsound:
        print("\n--- sample completeness GAPS (xolver unknown, oracles agree) ---")
        for smt, xo, z3, cv in gaps[:3]:
            print(f"[{z3}]\n{smt}")
    sys.exit(1 if unsound else 0)

if __name__ == "__main__":
    main()
