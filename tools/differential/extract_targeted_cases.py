#!/usr/bin/env python3
"""
Extract a targeted diagnostic corpus: per category (the directory containing the
.smt2), pick up to 3 sat + 3 unsat cases that the ORACLE solves but XOLVER fails.
Copies them into an independent folder preserving the original directory structure.
Pure data-processing (oracle cache + existing diff CSVs) — no xolver runs.
Python 3.7+, stdlib only.
"""
import csv, os, glob, shutil

ROOT = "/mnt/d/D_Study/BUAA/projects/NLColver"
os.chdir(ROOT)
BENCH = "benchmark/non-incremental"
DEC = {"sat", "unsat"}
FAIL = {"unknown", "timeout", "error", "", "to/none", "none"}

# logic -> (output_root, [diff_csv_globs])
PLAN = {
    "QF_NIA":     ("targeted_nia",   ["results/wallclock_d1/diff_QF_NIA_node*.csv"]),
    "QF_ANIA":    ("targeted_eqnia", ["results/2026-06-04_2226_nia2_combo/diff_QF_ANIA_node9.csv"]),
    "QF_AUFNIA":  ("targeted_eqnia", ["results/2026-06-04_2226_nia2_combo/diff_QF_AUFNIA_node9.csv"]),
    "QF_UFNIA":   ("targeted_eqnia", ["results/2026-06-04_1828_idle_0604/diff_QF_UFNIA_node9.csv"]),
    "QF_UFDTNIA": ("targeted_eqnia", ["results/2026-06-04_morning_batch/diff_QF_UFDTNIA_node14.csv"]),
}

# oracle: key -> verdict
orac = {}
for r in csv.reader(open("tools/oracle_cache.tsv"), delimiter="\t"):
    if len(r) >= 4 and r[2] in DEC:
        orac[r[0]] = r[2]

def load_xolver(globs):
    d = {}
    for g in globs:
        for p in glob.glob(g):
            with open(p) as f:
                rd = csv.DictReader(f)
                col = "xolver_default_verdict" if "xolver_default_verdict" in (rd.fieldnames or []) else \
                      ("candidate" if "candidate" in (rd.fieldnames or []) else None)
                if not col: continue
                for row in rd:
                    d[row["key"]] = row[col].strip().lower()
    return d

manifest = []
for logic, (outroot, globs) in PLAN.items():
    xol = load_xolver(globs)
    # category -> {sat:[], unsat:[]}  of (size, key)
    cats = {}
    for key, ov in orac.items():
        if not key.startswith(logic + "/"):
            continue
        xv = xol.get(key, "")            # missing => treat as candidate fail (agent re-verifies)
        if xv in DEC:                    # xolver already solves it -> not a target
            continue
        path = os.path.join(BENCH, key)
        if not os.path.isfile(path):
            continue
        rel = key[len(logic) + 1:]
        category = os.path.dirname(rel) or "(root)"
        cats.setdefault((logic, category), {"sat": [], "unsat": []})[ov].append((os.path.getsize(path), key, xv))
    for (lg, cat), d in cats.items():
        for pol in ("sat", "unsat"):
            for sz, key, xv in sorted(d[pol])[:3]:        # 3 smallest-failing per polarity
                src = os.path.join(BENCH, key)
                dst = os.path.join(outroot, key)          # preserve full structure under logic
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copy2(src, dst)
                manifest.append((lg, cat, pol, sz, orac[key], xv or "MISSING", key))

# manifests (one per output root)
for outroot in ("targeted_nia", "targeted_eqnia"):
    rows = [m for m in manifest if (outroot == "targeted_nia") == (m[0] == "QF_NIA")]
    with open(os.path.join(outroot, "MANIFEST.tsv"), "w") as f:
        f.write("logic\tcategory\tpolarity\tsize\toracle\txolver_was\tkey\n")
        for m in sorted(rows):
            f.write("\t".join(str(x) for x in m) + "\n")

# summary
from collections import Counter
print("=== extraction summary ===")
for outroot in ("targeted_nia", "targeted_eqnia"):
    rows = [m for m in manifest if (outroot == "targeted_nia") == (m[0] == "QF_NIA")]
    by_logic = Counter(m[0] for m in rows)
    ncat = len(set((m[0], m[1]) for m in rows))
    print(f"\n  {outroot}/  ({len(rows)} cases, {ncat} categories)")
    for lg, n in sorted(by_logic.items()):
        s = sum(1 for m in rows if m[0] == lg and m[2] == "sat")
        u = sum(1 for m in rows if m[0] == lg and m[2] == "unsat")
        cats = len(set(m[1] for m in rows if m[0] == lg))
        print(f"    {lg:12s} {n:4d} cases  ({s} sat, {u} unsat)  across {cats} categories")
print(f"\n  total extracted: {len(manifest)} cases")
print("  manifests: targeted_nia/MANIFEST.tsv  targeted_eqnia/MANIFEST.tsv")
