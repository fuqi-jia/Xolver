#!/usr/bin/env python3
# Differential fuzzer for NLColver array logics vs z3 + cvc5.
# Generates random small QF array formulas; flags any nlcolver verdict that
# DISAGREES with z3/cvc5 (unknown is allowed = sound-incomplete).
import random, subprocess, sys, tempfile, os

import os
NLC = os.environ.get("NLCOLVER", "build/bin/nlcolver")
Z3 = "/usr/local/bin/z3"
CVC5 = "/usr/bin/cvc5"

def run(cmd, f, timeout=10):
    try:
        if cmd is NLC:
            out = subprocess.run([cmd, "solve", f], capture_output=True, text=True, timeout=timeout)
        else:
            out = subprocess.run([cmd, f], capture_output=True, text=True, timeout=timeout)
        for line in out.stdout.splitlines():
            t = line.strip()
            if t in ("sat", "unsat", "unknown"):
                return t
        return "error"
    except subprocess.TimeoutExpired:
        return "timeout"
    except Exception:
        return "error"

def gen(logic, rng):
    # element/index sorts
    real = "LRA" in logic or "ALRA" in logic
    S = "Real" if real else "Int"
    def lit():
        return f"{rng.randint(0,4)}.0" if real else str(rng.randint(0,4))
    lines = [f"(set-logic {logic})"]
    arrs = [f"a{k}" for k in range(rng.randint(1,2))]
    idxs = [f"i{k}" for k in range(rng.randint(2,3))]
    elems = [f"e{k}" for k in range(rng.randint(2,3))]
    for a in arrs: lines.append(f"(declare-const {a} (Array {S} {S}))")
    for i in idxs: lines.append(f"(declare-const {i} {S})")
    for e in elems: lines.append(f"(declare-const {e} {S})")
    has_uf = "AUF" in logic
    if has_uf: lines.append(f"(declare-fun f ({S}) {S})")
    def idx_term():
        c = rng.random()
        if c < 0.4: return rng.choice(idxs)
        if c < 0.7: return lit()
        return f"(+ {rng.choice(idxs)} {lit()})" if not real else f"(+ {rng.choice(idxs)} {lit()})"
    def elem_term():
        c = rng.random()
        if c < 0.5: return rng.choice(elems)
        if c < 0.8: return lit()
        return f"(+ {rng.choice(elems)} {lit()})"
    def arr_term(depth=0):
        c = rng.random()
        if depth > 2 or c < 0.5:
            return rng.choice(arrs)
        if c < 0.85:
            return f"(store {arr_term(depth+1)} {idx_term()} {elem_term()})"
        return f"((as const (Array {S} {S})) {elem_term()})"
    def read():
        return f"(select {arr_term()} {idx_term()})"
    def bool_atom():
        c = rng.random()
        if c < 0.4:
            return f"(= {read()} {elem_term()})"
        if c < 0.55:
            return f"(= {read()} {read()})"
        if c < 0.7 and has_uf:
            return f"(= (f {read()}) {elem_term()})"
        if c < 0.82:
            return f"(= {rng.choice(arrs)} {arr_term(1)})"
        if c < 0.92:
            op = rng.choice(["<=", "<", ">", ">="])
            return f"({op} {read()} {lit()})"
        return f"(= {rng.choice(idxs)} {idx_term()})"
    n = rng.randint(2,5)
    for _ in range(n):
        atom = bool_atom()
        if rng.random() < 0.4: atom = f"(not {atom})"
        lines.append(f"(assert {atom})")
    lines.append("(check-sat)")
    return "\n".join(lines)

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    logics = ["QF_ALIA", "QF_ALRA", "QF_AUFLIA", "QF_AUFLRA"]
    rng = random.Random(seed)
    unsound = []; agree = 0; unk = 0; skipped = 0
    for n in range(count):
        logic = rng.choice(logics)
        smt = gen(logic, rng)
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fp:
            fp.write(smt); path = fp.name
        nlc = run(NLC, path); z = run(Z3, path); c = run(CVC5, path)
        os.unlink(path)
        # oracle: prefer agreement of z3 and cvc5
        if z in ("error","timeout") or c in ("error","timeout"):
            skipped += 1; continue
        if z != c:
            skipped += 1; continue   # oracles disagree (shouldn't), skip
        oracle = z
        if nlc == "unknown":
            unk += 1
        elif nlc in ("sat","unsat"):
            if nlc == oracle:
                agree += 1
            else:
                unsound.append((logic, nlc, oracle, smt))
        else:
            skipped += 1
    print(f"agree={agree} unknown={unk} skipped={skipped} UNSOUND={len(unsound)}")
    for (logic, nlc, oracle, smt) in unsound[:8]:
        print(f"\n===== UNSOUND ({logic}): nlcolver={nlc} oracle={oracle} =====")
        print(smt)
    sys.exit(1 if unsound else 0)

main()
