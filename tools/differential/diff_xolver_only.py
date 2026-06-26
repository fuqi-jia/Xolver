#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""diff_xolver_only.py -- incremental re-measure: re-run ONLY xolver, inherit oracle.

Stage-4 daily cycle (merge -> re-measure -> catalog) recomputes xolver verdicts after
every src change, but the oracle (z3/cvc5) verdict can't change -- the oracle binary and
the benchmark files are both fixed. So re-running the oracle column is pure waste (~50%+
of a full 3-way batch). This helper takes a baseline sqlite (produced by diff_ingest.py
from a prior full batch), re-runs xolver default + --allon for each case, and COPIES the
oracle_solver / oracle_verdict / oracle_time_ms straight from the baseline.

    python3 diff_xolver_only.py \\
        --baseline-sqlite results/2026-06-XX/full.sqlite \\
        --xolver build/bin/xolver --xolver-git-tip <new-tip> \\
        --out results/2026-06-YY/full_xolver_refresh.sqlite \\
        --candflags "XOLVER_EUF_PROP=1 XOLVER_NIA_LOCALSEARCH=1 ..." \\
        --panda-list 1,2,3,4,5,7,8,9,10,14 -j 200

Then diff_merge.py / diff_report.py run unchanged (same schema).

Schema: identical to diff_ingest.py (imported, never re-declared) plus the
`oracle_inherited_from_run` audit column -- the basename of the baseline sqlite a row's
oracle data came from (NULL = oracle ran fresh, e.g. a benchmark case not in the baseline).
All is_* derived flags are recomputed from the FRESH xolver verdicts vs the inherited
oracle, so any new disagreement (the soundness-audit basis) is flagged correctly.

Python 3.7+, stdlib only.
"""

import argparse
import csv
import datetime
import glob
import os
import re
import resource
import sqlite3
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

# Reuse the canonical schema + flag logic so there is zero drift.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from diff_ingest import SCHEMA, ALL_COLS, derive, _int  # noqa: E402

DECIDED = ("sat", "unsat")
CVC5_DIVISIONS = ("QF_DT", "QF_UFDTNIA")          # Hole-1 oracle routing (mirrors diff_common.sh)
VERDICT_RE = re.compile(r"unsat|unknown|sat", re.IGNORECASE)

# Baseline columns this tool reads (carried forward unchanged).
_CARRY = ("key", "division", "file_path", "file_size_bytes", "declared_logic",
          "oracle_solver", "oracle_verdict", "oracle_time_ms",
          "panda_node", "file_dir_prefix", "file_name_stem")


def now_iso():
    # timezone-aware UTC (3.7-safe; avoids the 3.12 utcnow() deprecation)
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _memlimit(memcap_kb):
    def _apply():
        try:
            n = int(memcap_kb) * 1024
            resource.setrlimit(resource.RLIMIT_AS, (n, n))
        except Exception:
            pass
    return _apply


def run_verdict(cmd, timeout, memcap_kb, extra_env=None):
    """Run one solver invocation -> (verdict, elapsed_ms). Mirrors diff_common.sh::verdict_timed."""
    env = dict(os.environ)
    if extra_env:
        env.update(extra_env)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                           timeout=timeout, env=env, preexec_fn=_memlimit(memcap_kb))
        out = p.stdout.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return "timeout", int((time.time() - t0) * 1000)
    except Exception:
        return "error", int((time.time() - t0) * 1000)
    ms = int((time.time() - t0) * 1000)
    m = VERDICT_RE.search(out)
    return (m.group(0).lower() if m else "error"), ms


def parse_candflags(s):
    """'A=1 B=2' -> {'A':'1','B':'2'}."""
    env = {}
    for tok in (s or "").split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            env[k] = v
    return env


def oracle_for_division(div):
    return "cvc5" if div in CVC5_DIVISIONS else "z3"


def file_meta(path, division):
    """Reconstruct size / declared_logic / dir_prefix / stem for a NEW (non-baseline) case."""
    try:
        size = os.path.getsize(path)
    except OSError:
        size = 0
    decl = ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = re.search(r"set-logic\s+([A-Za-z_0-9]+)", line)
                if m:
                    decl = m.group(1)
                    break
    except OSError:
        pass
    base = os.path.basename(path)
    stem = base[:-5] if base.endswith(".smt2") else base
    key = "%s/%s" % (division, path.split(division + "/", 1)[-1]) if (division + "/") in path else "%s/%s" % (division, base)
    rel = key[len(division) + 1:]
    parts = rel.split("/")[:-1]            # dir components
    dir_prefix = "/".join(parts[:2])
    return key, size, decl, dir_prefix, stem


def load_baseline(paths, panda_filter):
    """key -> (row dict, source_basename). First db wins on duplicate keys."""
    rows = {}
    for db in paths:
        if not os.path.exists(db):
            sys.stderr.write("  [baseline] skip missing %s\n" % db)
            continue
        src = os.path.basename(db)
        conn = sqlite3.connect(db)
        conn.row_factory = sqlite3.Row
        try:
            for r in conn.execute("SELECT %s FROM diff_results" % ",".join(_CARRY)):
                key = r["key"]
                if key in rows:
                    continue
                node = _int(r["panda_node"], default=-1)
                if panda_filter is not None and node not in panda_filter:
                    continue
                rows[key] = ({k: r[k] for k in _CARRY}, src)
        finally:
            conn.close()
    return rows


def build_row(base, src, dv, dvm, av, avm, git_tip, ts,
              oracle_solver=None, oracle_verdict=None, oracle_ms=None, inherited=None):
    row = {
        "key": base["key"], "division": base["division"], "file_path": base["file_path"],
        "file_size_bytes": _int(base["file_size_bytes"]), "declared_logic": base["declared_logic"],
        "xolver_default_verdict": dv, "xolver_default_time_ms": dvm,
        "xolver_allon_verdict": av, "xolver_allon_time_ms": avm,
        "oracle_solver": oracle_solver if oracle_solver is not None else base["oracle_solver"],
        "oracle_verdict": oracle_verdict if oracle_verdict is not None else base["oracle_verdict"],
        "oracle_time_ms": _int(oracle_ms if oracle_ms is not None else base["oracle_time_ms"]),
        "panda_node": _int(base["panda_node"], default=-1),
        "run_timestamp": ts, "xolver_git_tip": git_tip,
        "file_dir_prefix": base["file_dir_prefix"], "file_name_stem": base["file_name_stem"],
        "oracle_inherited_from_run": inherited,
    }
    row.update(derive(row))
    return row


def resolve_path(file_path, key, bench):
    if os.path.exists(file_path):
        return file_path
    if bench:
        cand = os.path.join(bench, key)
        if os.path.exists(cand):
            return cand
    return file_path  # let the solver error out, recorded as 'error'


def main():
    ap = argparse.ArgumentParser(description="Incremental xolver-only re-measure (oracle inherited).")
    ap.add_argument("--baseline-sqlite", nargs="+", required=True,
                    help="baseline sqlite db(s) or glob(s) with oracle verdicts")
    ap.add_argument("--xolver", required=True, help="new xolver binary")
    ap.add_argument("--xolver-git-tip", default="unknown")
    ap.add_argument("--out", required=True, help="output refreshed sqlite")
    ap.add_argument("--csv-mirror", default=None)
    ap.add_argument("--candflags", default=os.environ.get("CANDFLAGS", ""),
                    help="--allon env assignments 'A=1 B=2' (default: $CANDFLAGS)")
    ap.add_argument("--panda-list", default=None, help="comma list of panda_node to refresh (default: all)")
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--memcap-kb", type=int, default=16000000)
    ap.add_argument("-j", "--jobs", type=int, default=8)
    ap.add_argument("--bench", default=None,
                    help="benchmark/non-incremental dir: relocate moved files AND discover "
                         "new cases not in baseline (those run the full 3-way, oracle fresh)")
    args = ap.parse_args()

    # expand globs
    bpaths = []
    for pat in args.baseline_sqlite:
        bpaths.extend(sorted(glob.glob(pat)) or [pat])
    panda_filter = None
    if args.panda_list:
        panda_filter = set(int(x) for x in args.panda_list.split(",") if x.strip())

    if not os.path.exists(args.xolver):
        sys.stderr.write("ERROR: xolver not found: %s\n" % args.xolver)
        sys.exit(1)

    candenv = parse_candflags(args.candflags)
    ts = now_iso()
    baseline = load_baseline(bpaths, panda_filter)
    sys.stderr.write("  [baseline] %d cases from %d db(s)%s\n" % (
        len(baseline), len(bpaths),
        ("" if panda_filter is None else " (panda %s)" % sorted(panda_filter))))

    def refresh_one(item):
        key, (base, src) = item
        path = resolve_path(base["file_path"], key, args.bench)
        dv, dvm = run_verdict([args.xolver, "solve", path], args.timeout, args.memcap_kb)
        av, avm = run_verdict([args.xolver, "solve", path], args.timeout, args.memcap_kb,
                              extra_env=candenv)
        return build_row(base, src, dv, dvm, av, avm, args.xolver_git_tip, ts, inherited=src)

    out_rows = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
        for row in ex.map(refresh_one, list(baseline.items())):
            out_rows.append(row)

    # Optional: discover NEW benchmark cases not in baseline -> full 3-way, oracle fresh.
    new_count = 0
    if args.bench:
        z3 = os.environ.get("Z3", "z3")
        cvc5 = os.environ.get("CVC5", "cvc5")
        divisions = sorted(set(b[0]["division"] for b in baseline.values()))
        known = set(baseline.keys())
        for div in divisions:
            ddir = os.path.join(args.bench, div)
            if not os.path.isdir(ddir):
                continue
            for root, _d, files in os.walk(ddir):
                for fn in files:
                    if not fn.endswith(".smt2"):
                        continue
                    p = os.path.join(root, fn)
                    rel = os.path.relpath(p, ddir)
                    key = "%s/%s" % (div, rel)
                    if key in known:
                        continue
                    new_count += 1
                    _k, size, decl, dprefix, stem = file_meta(p, div)
                    osolver = oracle_for_division(div)
                    if osolver == "cvc5":
                        ocmd = [cvc5, "--tlimit=%d" % (args.timeout * 1000), p]
                    else:
                        ocmd = [z3, p]
                    dv, dvm = run_verdict([args.xolver, "solve", p], args.timeout, args.memcap_kb)
                    av, avm = run_verdict([args.xolver, "solve", p], args.timeout, args.memcap_kb,
                                          extra_env=candenv)
                    ov, ovm = run_verdict(ocmd, args.timeout, args.memcap_kb)
                    base = {"key": key, "division": div, "file_path": p,
                            "file_size_bytes": size, "declared_logic": decl,
                            "oracle_solver": osolver, "oracle_verdict": ov, "oracle_time_ms": ovm,
                            "panda_node": -1, "file_dir_prefix": dprefix, "file_name_stem": stem}
                    out_rows.append(build_row(base, None, dv, dvm, av, avm,
                                              args.xolver_git_tip, ts,
                                              oracle_solver=osolver, oracle_verdict=ov,
                                              oracle_ms=ovm, inherited=None))

    # write
    out_dir = os.path.dirname(args.out)
    if out_dir and not os.path.isdir(out_dir):
        os.makedirs(out_dir)
    conn = sqlite3.connect(args.out)
    try:
        conn.executescript(SCHEMA)
        sql = "INSERT OR REPLACE INTO diff_results (%s) VALUES (%s)" % (
            ",".join(ALL_COLS), ",".join(["?"] * len(ALL_COLS)))
        conn.executemany(sql, [tuple(r.get(c) for c in ALL_COLS) for r in out_rows])
        conn.commit()
        n = conn.execute("SELECT COUNT(*) FROM diff_results").fetchone()[0]
        dis = conn.execute("SELECT COUNT(*) FROM diff_results WHERE is_disagreement=1").fetchone()[0]
    finally:
        conn.close()

    sys.stderr.write("  [refresh] %d cases (%d inherited oracle, %d new fresh-oracle) -> %s\n"
                     % (n, len(baseline), new_count, args.out))
    sys.stderr.write("  [refresh] disagreements (xolver vs inherited oracle): %d%s\n"
                     % (dis, "  <- TRIAGE" if dis else ""))

    if args.csv_mirror:
        with open(args.csv_mirror, "w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(ALL_COLS)
            for r in out_rows:
                w.writerow([r.get(c) for c in ALL_COLS])


if __name__ == "__main__":
    main()
