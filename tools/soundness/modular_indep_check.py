#!/usr/bin/env python3
"""Independent residue-UNSAT cross-check for the modular reasoner's oracle-blind
UNSATs (Track A). FULLY INDEPENDENT of Xolver's C++ modular reasoner AND its
kernel evaluator: parses the dumped normalized constraints and brute-forces the
residue space over Z/m with its OWN Python evaluator.

Soundness (subset argument). Any integer solution projects mod m to a residue
assignment that:
  - satisfies every EQUALITY (p = 0 => p == 0 mod m), and
  - satisfies every Neq `a*v + c != 0` where v is a variable PROVABLY BOUNDED to
    [0, ub] with ub < m (then v's value == its residue, so the disequality is an
    exact residue condition).
We deliberately use ONLY these two constraint kinds (and ONLY Neqs on bounded
vars) — a SUBSET of the system. If NO residue assignment in Z/m satisfies this
subset, the FULL system is UNSAT (adding the omitted inequalities only removes
solutions). => a "no residue model" result INDEPENDENTLY CONFIRMS UNSAT. We never
include a Neq on an unbounded var (that would over-constrain and risk a false
confirmation). If a residue model of the subset exists, the result is
INCONCLUSIVE (the reasoner may exploit structure this subset omits) — never a
disagreement, since residue analysis cannot prove the integer system SAT.

Python 3.7+, stdlib only. stdin = NIA_DOM_DIAG text (`  reason=R rel=REL poly=P`,
rel: 0=Eq 1=Neq 2=Lt 3=Leq 4=Gt 5=Geq); argv[1] = modulus m.
"""
import sys
import re
import itertools

def parse_poly(s):
    """flat sum -> list of (coeff:int, {var:exp})."""
    s = s.replace('(', ' ').replace(')', ' ')
    s = re.sub(r'\s+', ' ', s).strip()
    parts = re.findall(r'[+\-]|[^+\-]+', s)
    signed, sign = [], 1
    for p in parts:
        p = p.strip()
        if p == '+':
            sign = 1
        elif p == '-':
            sign = -1
        elif p:
            signed.append((sign, p)); sign = 1
    monos = []
    for sg, term in signed:
        factors = [f.strip() for f in term.split('*') if f.strip()]
        coeff, powers = sg, {}
        for f in factors:
            if re.fullmatch(r'\d+', f):
                coeff *= int(f)
            else:
                mm = re.fullmatch(r'(.+?)\^(\d+)', f)
                v, e = (mm.group(1), int(mm.group(2))) if mm else (f, 1)
                powers[v] = powers.get(v, 0) + e
        monos.append((coeff, powers))
    return monos

def eval_mod(monos, assign, m):
    tot = 0
    for coeff, powers in monos:
        t = coeff % m
        for v, e in powers.items():
            t = (t * pow(assign[v] % m, e, m)) % m
        tot = (tot + t) % m
    return tot % m

def lin_single(monos):
    """If poly is a*v + c with a single var v (degree 1), return (v,a,c) else None."""
    a = None; v = None; c = 0
    for coeff, powers in monos:
        if not powers:
            c += coeff
        elif len(powers) == 1 and list(powers.values())[0] == 1:
            if v is not None and v != list(powers.keys())[0]:
                return None
            v = list(powers.keys())[0]; a = (a or 0) + coeff
        else:
            return None
    if v is None:
        return None
    return (v, a, c)

def main():
    m = int(sys.argv[1])
    cons = []  # (rel, monos)
    for line in sys.stdin:
        mm = re.search(r'rel=(\d+)\s+poly=(.*)$', line.strip())
        if mm:
            cons.append((int(mm.group(1)), parse_poly(mm.group(2))))
    # bound detection: lb (from -v<=0) and ub (from v-c<=0 / v-c<0)
    lb, ub = {}, {}
    for rel, monos in cons:
        ls = lin_single(monos)
        if not ls:
            continue
        v, a, c = ls
        if rel == 3:  # Leq: a*v + c <= 0
            if a == -1:                      # -v + c <= 0 -> v >= c
                lb[v] = max(lb.get(v, -10**9), c)
            elif a == 1:                     # v + c <= 0 -> v <= -c
                ub[v] = min(ub.get(v, 10**9), -c)
        elif rel == 2:  # Lt
            if a == 1:                       # v + c < 0 -> v <= -c-1
                ub[v] = min(ub.get(v, 10**9), -c - 1)
    bounded = {v for v in ub if lb.get(v, None) == 0 and ub[v] < m and ub[v] >= 0}

    eqs = [monos for rel, monos in cons if rel == 0]
    neqs = []  # (v, target) for Neq on a bounded var: a*v+c != 0 -> v != -c/a
    for rel, monos in cons:
        if rel != 1:
            continue
        ls = lin_single(monos)
        if not ls:
            continue
        v, a, c = ls
        if v in bounded and a in (1, -1) and ((-c) % a == 0):
            neqs.append((v, ((-c) // a) % m))
    relvars = sorted({v for monos in eqs for _, powers in monos for v in powers}
                     | {v for v, _ in neqs})
    if not eqs and not neqs:
        print("INCONCLUSIVE no-residue-constraints"); return
    if m ** len(relvars) > 5_000_000:
        print("INCONCLUSIVE too-many-tuples vars=%d m=%d" % (len(relvars), m)); return
    for combo in itertools.product(range(m), repeat=len(relvars)):
        a = dict(zip(relvars, combo))
        if all(eval_mod(monos, a, m) == 0 for monos in eqs) and \
           all(a[v] % m != t for v, t in neqs):
            print("INCONCLUSIVE residue-model-exists (subset SAT)"); return
    print("CONFIRMED-UNSAT eqs=%d neqs=%d vars=%d m=%d" % (len(eqs), len(neqs), len(relvars), m))

if __name__ == '__main__':
    main()
