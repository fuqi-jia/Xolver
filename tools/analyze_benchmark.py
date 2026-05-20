#!/usr/bin/env python3
"""
NLColver Benchmark Delta Analyzer

Reads two benchmark runs (current + baseline) and produces compact,
actionable analysis artifacts for Git commit.

Usage:
    python tools/analyze_benchmark.py \
        --current /data/bench-runs/2026-05-20_1530_nlcolver_abc1234 \
        --baseline /data/bench-runs/2026-05-19_2100_nlcolver_def4567 \
        --z3-baseline /data/bench-baselines/z3_4.12.2_xxx_t10.json \
        --output bench-results/runs/2026-05-20_1530_nlcolver_abc1234
"""

import argparse
import csv
import hashlib
import json
import os
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# Size budgets (enforced after generation)
# ---------------------------------------------------------------------------
MAX_ROWS = {
    "regressions_top": 200,
    "unknown_top": 50,
    "timeout_top": 50,
    "slow_top": 50,
    "selected_cases": 50,
}
MAX_FIELD_LEN = {
    "stderr_tail": 1024,
    "unknown_detail": 512,
    "suggested_debug": 512,
}
MAX_GIT_PAYLOAD_BYTES = 1024 * 1024  # 1 MB hard cap


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class CaseRecord:
    file: str
    logic: str
    category: str
    result: str
    time: float
    old_result: str = ""
    old_time: float = 0.0
    z3_result: str = ""
    z3_time: float = 0.0
    stats: dict = field(default_factory=dict)
    stats_source: str = "none"
    returncode: int = 0
    signal: str = ""
    killed_by_timeout: bool = False
    stderr_tail: str = ""
    expected: str = ""  # benchmark expected status if known


# ---------------------------------------------------------------------------
# Manifest helpers
# ---------------------------------------------------------------------------

def load_manifest(run_dir: Path) -> Tuple[Optional[str], Optional[Set[str]]]:
    """Load manifest.txt and return (hash, set of files)."""
    manifest_path = run_dir / "manifest.txt"
    if not manifest_path.exists():
        return None, None
    files = set()
    with open(manifest_path) as f:
        for line in f:
            line = line.strip()
            if line:
                files.add(line)
    return None, files


def manifest_relation(current_files: Set[str], baseline_files: Set[str]) -> str:
    if current_files == baseline_files:
        return "exact"
    if current_files < baseline_files:
        return "subset"
    if current_files & baseline_files:
        return "intersection"
    return "invalid"


# ---------------------------------------------------------------------------
# Loaders
# ---------------------------------------------------------------------------

def load_statistics(path: Path) -> dict:
    with open(path) as f:
        return json.load(f)


def load_frozen_baseline(path: Path) -> dict:
    """Load a frozen Z3/CVC5 baseline JSON."""
    with open(path) as f:
        return json.load(f)


# ---------------------------------------------------------------------------
# Classification logic
# ---------------------------------------------------------------------------

def classify_mismatch(
    current: str, old: str, z3: str, expected: str
) -> str:
    """
    confirmed_mismatch: expected is sat/unsat and current disagrees
    regression_disagreement: old was sat/unsat and current is the opposite
    solver_disagreement: z3 is sat/unsat and current disagrees (expected unknown)
    """
    definitive = {"sat", "unsat"}
    if expected in definitive and current in definitive and current != expected:
        return "confirmed_mismatch"
    if old in definitive and current in definitive and old != current:
        return "regression_disagreement"
    if z3 in definitive and current in definitive and z3 != current:
        return "solver_disagreement"
    return "none"


def is_regression(current: str, old: str, new_time: float, old_time: float) -> Optional[str]:
    """Return regression type string or None."""
    solved = {"sat", "unsat"}
    if old in solved and current == "timeout":
        return "solved_to_timeout"
    if old in solved and current == "unknown":
        return "solved_to_unknown"
    if old in solved and current == "error":
        return "solved_to_error"
    if old in solved and current in solved and old != current:
        return "wrong_answer"
    if old_time > 0 and new_time / old_time >= 3.0 and (new_time - old_time) >= 0.5:
        return "slowdown"
    return None


def is_solving_improvement(current: str, old: str) -> bool:
    no_answer = {"timeout", "unknown", "error", "killed"}
    solved = {"sat", "unsat"}
    return old in no_answer and current in solved


def is_stability_improvement(current: str, old: str) -> bool:
    return old == "error" and current in {"timeout", "unknown", "killed"}


def is_mismatch_fixed(current: str, old: str, z3: str) -> bool:
    if old in {"sat", "unsat"} and z3 in {"sat", "unsat"} and old != z3:
        return current == z3
    return False


def crash_signature(stderr_tail: str, returncode: int, signal: str) -> str:
    """Extract a short crash signature for clustering."""
    if signal:
        return f"signal:{signal}"
    if returncode == -11:
        return "SIGSEGV"
    if returncode == -6:
        return "SIGABRT"
    lines = stderr_tail.strip().splitlines()
    for line in reversed(lines[-5:]):
        line = line.strip()
        if "Assertion" in line or "assertion" in line.lower():
            return line[:120]
        if "Segmentation fault" in line or "SIGSEGV" in line:
            return "SIGSEGV"
        if "std::" in line and "exception" in line.lower():
            return line[:120]
    return f"exit:{returncode}"


# ---------------------------------------------------------------------------
# Clustering
# ---------------------------------------------------------------------------

def cluster_key(record: CaseRecord) -> str:
    logic = record.logic
    cat = record.category
    code = record.stats.get("unknown_code", "none")
    atoms = record.stats.get("sat", {}).get("vars", 0)
    size_bucket = "small" if atoms < 100 else "medium" if atoms < 500 else "large"
    return f"{logic}/{cat}/{code}/{size_bucket}"


def pick_representative(records: List[CaseRecord]) -> CaseRecord:
    """Pick the most representative case from a cluster."""
    # Prefer cases with stats, then shortest filename, then first
    with_stats = [r for r in records if r.stats]
    if with_stats:
        records = with_stats
    records.sort(key=lambda r: len(r.file))
    return records[0]


# ---------------------------------------------------------------------------
# Writers
# ---------------------------------------------------------------------------

def write_csv_dicts(path: Path, rows: List[dict], fieldnames: List[str]):
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row.get(k, "") for k in fieldnames})


def write_jsonl(path: Path, records: List[dict]):
    with open(path, "w") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")


def write_action_items(path: Path, analysis: dict):
    with open(path, "w") as f:
        f.write("# Action Items\n\n")
        f.write(f"Run: {analysis['run_id']}\n")
        f.write(f"Baseline: {analysis.get('baseline_run_id', 'none')}\n")
        f.write(f"Manifest relation: {analysis.get('manifest_relation', 'unknown')}\n")
        if analysis.get('manifest_relation') == 'invalid':
            f.write("\n**WARNING: baseline manifest does not match. Delta analysis may be unreliable.**\n")
        f.write("\n")

        # P0
        f.write("## P0: Wrong answer\n\n")
        p0 = analysis.get("p0", [])
        if not p0:
            f.write("No new confirmed mismatch or regression disagreement.\n\n")
        else:
            for item in p0[:10]:
                f.write(f"- `{item['file']}`: {item['old']} -> {item['new']}\n")
                f.write(f"  Classification: {item.get('classification', 'mismatch')}\n")
            f.write("\n")

        # P1
        f.write("## P1: Crash / Error\n\n")
        p1 = analysis.get("p1", [])
        if not p1:
            f.write("No new crashes.\n\n")
        else:
            sig_groups = defaultdict(list)
            for item in p1:
                sig_groups[item.get('crash_signature', 'unknown')].append(item)
            for sig, items in sig_groups.items():
                f.write(f"- Signature: `{sig}` ({len(items)} cases)\n")
                rep = items[0]
                f.write(f"  Suspected component: {rep.get('suspected_component', 'unknown')}\n")
                f.write(f"  Evidence: {rep.get('evidence', {})}\n")
                f.write(f"  Representative: {rep['file']}\n")
            f.write("\n")

        # P2
        f.write("## P2: Timeout regression\n\n")
        p2 = analysis.get("p2", [])
        if not p2:
            f.write("No new solved->timeout regressions.\n\n")
        else:
            clusters = defaultdict(list)
            for item in p2:
                clusters[item.get('category_cluster', 'unknown')].append(item)
            for clust, items in clusters.items():
                f.write(f"- Cluster `{clust}`: {len(items)} cases\n")
                rep = items[0]
                f.write(f"  Evidence: {rep.get('evidence', {})}\n")
                f.write(f"  Suspected component: {rep.get('suspected_component', 'unknown')}\n")
                f.write(f"  Suggested debug: {rep.get('suggested_debug', 'none')}\n")
                f.write(f"  Representative: {rep['file']}\n")
            f.write("\n")

        # P3
        f.write("## P3: Unknown regression\n\n")
        p3 = analysis.get("p3", [])
        if not p3:
            f.write("No new solved->unknown regressions.\n\n")
        else:
            for item in p3[:10]:
                f.write(f"- `{item['file']}`: {item['old']} -> {item['new']}\n")
            f.write("\n")

        # Summary
        f.write("## Summary\n\n")
        f.write(f"- Total files: {analysis.get('total_files', 0)}\n")
        f.write(f"- Regressions: {analysis.get('num_regressions', 0)}\n")
        f.write(f"- Solving improvements: {analysis.get('num_solving_improvements', 0)}\n")
        f.write(f"- Stability improvements: {analysis.get('num_stability_improvements', 0)}\n")
        f.write(f"- New crashes: {analysis.get('num_new_crashes', 0)}\n")
        f.write(f"- Mismatches: {analysis.get('num_mismatches', 0)}\n")


def write_summary_md(path: Path, analysis: dict):
    with open(path, "w") as f:
        f.write("# Benchmark Run Summary\n\n")
        f.write(f"Run: {analysis['run_id']}\n")
        f.write(f"Commit: {analysis.get('commit', 'unknown')}\n")
        f.write(f"Timeout: {analysis.get('timeout_sec', 'unknown')}s\n")
        f.write(f"Total: {analysis.get('total_files', 0)}\n\n")

        # Overall table
        f.write("## Overall\n\n")
        f.write("| Result | Count |\n")
        f.write("|---|---:|\n")
        for res in ["sat", "unsat", "unknown", "timeout", "error", "killed"]:
            cnt = analysis.get("current_counts", {}).get(res, 0)
            if cnt:
                f.write(f"| {res} | {cnt} |\n")
        f.write("\n")

        # Delta vs baseline
        if analysis.get("baseline_run_id"):
            f.write("## Delta vs Baseline\n\n")
            f.write("| Metric | Previous | Current | Delta |\n")
            f.write("|---|---:|---:|---:|\n")
            for metric, vals in analysis.get("delta_counts", {}).items():
                f.write(f"| {metric} | {vals['old']} | {vals['new']} | {vals['delta']:+d} |\n")
            f.write("\n")

        # Top regressions
        f.write("## Top Regression Clusters\n\n")
        clusters = analysis.get("regression_clusters", [])
        if not clusters:
            f.write("None.\n\n")
        else:
            for c in clusters[:10]:
                f.write(f"- `{c['cluster']}`: {c['count']} cases\n")
            f.write("\n")

        # Top improvements
        f.write("## Top Improvement Clusters\n\n")
        imp_clusters = analysis.get("improvement_clusters", [])
        if not imp_clusters:
            f.write("None.\n\n")
        else:
            for c in imp_clusters[:10]:
                f.write(f"- `{c['cluster']}`: {c['count']} cases\n")
            f.write("\n")


# ---------------------------------------------------------------------------
# Main analysis logic
# ---------------------------------------------------------------------------

def build_case_records(current_data: dict, baseline_data: Optional[dict], z3_data: Optional[dict]) -> List[CaseRecord]:
    current_results = {r["file"]: r for r in current_data.get("results", [])}
    baseline_results = {r["file"]: r for r in baseline_data.get("results", [])} if baseline_data else {}
    z3_results = {r["file"]: r for r in z3_data.get("results", [])} if z3_data else {}

    records = []
    for fpath, cur in current_results.items():
        # Extract logic and category from file path
        parts = fpath.replace("benchmark/non-incremental/", "").split("/")
        logic = parts[0] if len(parts) > 0 else "unknown"
        category = parts[1] if len(parts) > 1 else "root"

        base = baseline_results.get(fpath, {})
        z3 = z3_results.get(fpath, {})
        stats = cur.get("stats", {})

        rec = CaseRecord(
            file=fpath,
            logic=logic,
            category=category,
            result=cur.get("nlcolver_result", "unknown"),
            time=cur.get("nlcolver_time", 0.0),
            old_result=base.get("nlcolver_result", ""),
            old_time=base.get("nlcolver_time", 0.0),
            z3_result=z3.get("result", "") if isinstance(z3, dict) else "",
            z3_time=z3.get("time", 0.0) if isinstance(z3, dict) else 0.0,
            stats=stats,
            stats_source=cur.get("stats_source", "none"),
            returncode=cur.get("returncode", 0),
            signal=cur.get("signal", ""),
            killed_by_timeout=cur.get("killed_by_timeout", False),
            stderr_tail=cur.get("stderr_tail", ""),
        )
        records.append(rec)
    return records


def analyze(records: List[CaseRecord], current_data: dict, baseline_data: Optional[dict],
            manifest_relation: str, args) -> dict:
    analysis = {
        "run_id": args.run_id,
        "baseline_run_id": args.baseline_run_id if baseline_data else None,
        "manifest_relation": manifest_relation,
        "commit": args.commit,
        "timeout_sec": args.timeout,
        "total_files": len(records),
        "current_counts": defaultdict(int),
        "delta_counts": {},
        "regressions": [],
        "solving_improvements": [],
        "stability_improvements": [],
        "new_crashes": [],
        "mismatches": [],
        "p0": [],
        "p1": [],
        "p2": [],
        "p3": [],
    }

    for r in records:
        analysis["current_counts"][r.result] += 1

        # Mismatch classification
        mismatch_cls = classify_mismatch(r.result, r.old_result, r.z3_result, r.expected)
        if mismatch_cls != "none":
            analysis["mismatches"].append({
                "file": r.file,
                "current": r.result,
                "old": r.old_result,
                "z3": r.z3_result,
                "classification": mismatch_cls,
            })
            if mismatch_cls in ("confirmed_mismatch", "regression_disagreement"):
                analysis["p0"].append({
                    "file": r.file,
                    "old": f"{r.old_result} {r.old_time:.2f}s",
                    "new": f"{r.result} {r.time:.2f}s",
                    "classification": mismatch_cls,
                })

        # Regression
        reg_type = is_regression(r.result, r.old_result, r.time, r.old_time)
        if reg_type:
            rec = {
                "file": r.file,
                "logic": r.logic,
                "category": r.category,
                "old": r.old_result,
                "old_time": r.old_time,
                "new": r.result,
                "new_time": r.time,
                "reg_type": reg_type,
                "unknown_code": r.stats.get("unknown_code", ""),
                "category_cluster": cluster_key(r),
                "suspected_component": r.stats.get("unknown_component", ""),
                "evidence": {
                    "conflicts": r.stats.get("sat", {}).get("conflicts", 0),
                    "theory_conflicts": r.stats.get("theory", {}).get("conflicts", 0),
                    "avg_clause_size": r.stats.get("theory", {}).get("avg_conflict_size", 0),
                },
                "suggested_debug": "",
            }
            analysis["regressions"].append(rec)
            if reg_type == "solved_to_timeout":
                analysis["p2"].append(rec)
            elif reg_type == "solved_to_unknown":
                analysis["p3"].append(rec)

        # Crash
        if r.result == "error" and r.old_result != "error":
            sig = crash_signature(r.stderr_tail, r.returncode, r.signal)
            analysis["new_crashes"].append({
                "file": r.file,
                "logic": r.logic,
                "category": r.category,
                "returncode": r.returncode,
                "signal": r.signal,
                "crash_signature": sig,
                "suspected_component": r.stats.get("unknown_component", ""),
                "stderr_tail_hash": hashlib.sha256(r.stderr_tail.encode()).hexdigest()[:16],
            })
            analysis["p1"].append({
                "file": r.file,
                "crash_signature": sig,
                "suspected_component": r.stats.get("unknown_component", ""),
                "evidence": {"returncode": r.returncode, "signal": r.signal},
            })

        # Improvement
        if is_solving_improvement(r.result, r.old_result):
            analysis["solving_improvements"].append({
                "file": r.file,
                "old": r.old_result,
                "old_time": r.old_time,
                "new": r.result,
                "new_time": r.time,
            })
        elif is_stability_improvement(r.result, r.old_result):
            analysis["stability_improvements"].append({
                "file": r.file,
                "old": r.old_result,
                "new": r.result,
            })

    # Delta counts
    if baseline_data:
        old_counts = defaultdict(int)
        for r in records:
            if r.old_result:
                old_counts[r.old_result] += 1
        for metric in ["sat", "unsat", "unknown", "timeout", "error", "killed"]:
            old_v = old_counts.get(metric, 0)
            new_v = analysis["current_counts"].get(metric, 0)
            analysis["delta_counts"][metric] = {
                "old": old_v,
                "new": new_v,
                "delta": new_v - old_v,
            }

    # Cluster regressions
    reg_clusters = defaultdict(int)
    for r in analysis["regressions"]:
        reg_clusters[r["category_cluster"]] += 1
    analysis["regression_clusters"] = [
        {"cluster": k, "count": v} for k, v in sorted(reg_clusters.items(), key=lambda x: -x[1])
    ]

    # Cluster improvements
    imp_clusters = defaultdict(int)
    for r in analysis["solving_improvements"]:
        key = f"{r['file'].split('/')[0]}/{r['file'].split('/')[1] if len(r['file'].split('/')) > 1 else 'root'}"
        imp_clusters[key] += 1
    analysis["improvement_clusters"] = [
        {"cluster": k, "count": v} for k, v in sorted(imp_clusters.items(), key=lambda x: -x[1])
    ]

    analysis["num_regressions"] = len(analysis["regressions"])
    analysis["num_solving_improvements"] = len(analysis["solving_improvements"])
    analysis["num_stability_improvements"] = len(analysis["stability_improvements"])
    analysis["num_new_crashes"] = len(analysis["new_crashes"])
    analysis["num_mismatches"] = len(analysis["mismatches"])

    return analysis


def enforce_budgets(analysis: dict, output_dir: Path) -> int:
    """Trim output files to stay under MAX_GIT_PAYLOAD_BYTES. Returns final size."""
    # Write all files first
    write_action_items(output_dir / "action_items.md", analysis)
    write_summary_md(output_dir / "summary.md", analysis)

    # regressions_top.csv
    regs = analysis["regressions"]
    if len(regs) > MAX_ROWS["regressions_top"]:
        regs = regs[:MAX_ROWS["regressions_top"]]
    write_csv_dicts(
        output_dir / "regressions_top.csv", regs,
        ["file", "logic", "category", "old", "new", "reg_type",
         "category_cluster", "suspected_component", "evidence"]
    )

    # regressions_by_cluster.csv
    write_csv_dicts(
        output_dir / "regressions_by_cluster.csv",
        analysis["regression_clusters"],
        ["cluster", "count"]
    )

    # solving_improvements_top.csv
    simps = analysis["solving_improvements"]
    if len(simps) > MAX_ROWS["regressions_top"]:
        simps = simps[:MAX_ROWS["regressions_top"]]
    write_csv_dicts(
        output_dir / "solving_improvements_top.csv", simps,
        ["file", "old", "old_time", "new", "new_time"]
    )

    # stability_improvements_top.csv
    write_csv_dicts(
        output_dir / "stability_improvements_top.csv",
        analysis["stability_improvements"],
        ["file", "old", "new"]
    )

    # new_crashes.csv
    crashes = analysis["new_crashes"]
    write_csv_dicts(
        output_dir / "new_crashes.csv", crashes,
        ["file", "logic", "category", "returncode", "signal",
         "crash_signature", "suspected_component", "stderr_tail_hash"]
    )

    # mismatches.csv
    write_csv_dicts(
        output_dir / "mismatches.csv",
        analysis["mismatches"],
        ["file", "current", "old", "z3", "classification"]
    )

    # unknown_top / timeout_top / slow_top
    def write_top(path, records, key):
        sort_key = "new_time" if key in ("slow", "timeout", "unknown") else "time"
        rows = sorted(records, key=lambda r: r.get(sort_key, 0), reverse=True)
        if len(rows) > MAX_ROWS["unknown_top"]:
            rows = rows[:MAX_ROWS["unknown_top"]]
        write_csv_dicts(path, rows, ["file", "logic", "category", "new_time", "unknown_code"])

    unknowns = [r for r in analysis["regressions"] if r["new"] == "unknown"]
    write_top(output_dir / "unknown_top.csv", unknowns, "unknown")

    timeouts = [r for r in analysis["regressions"] if r["new"] == "timeout"]
    write_top(output_dir / "timeout_top.csv", timeouts, "timeout")

    # selected_cases.jsonl
    selected = []
    # P0 first
    for item in analysis["p0"][:10]:
        selected.append({
            "priority": 0,
            "file": item["file"],
            "type": item["classification"],
            "old": item["old"],
            "new": item["new"],
        })
    # P1
    for item in analysis["p1"][:10]:
        selected.append({
            "priority": 1,
            "file": item["file"],
            "type": "crash",
            "crash_signature": item.get("crash_signature", ""),
            "suspected_component": item.get("suspected_component", ""),
            "evidence": item.get("evidence", {}),
        })
    # P2
    for item in analysis["p2"][:20]:
        selected.append({
            "priority": 2,
            "file": item["file"],
            "type": "timeout_regression",
            "old": f"{item['old']} {item['old_time']:.2f}s",
            "new": f"{item['new']} {item['new_time']:.2f}s",
            "category_cluster": item.get("category_cluster", ""),
            "suspected_component": item.get("suspected_component", ""),
            "evidence": item.get("evidence", {}),
            "suggested_debug": item.get("suggested_debug", ""),
        })
    # P3
    for item in analysis["p3"][:10]:
        selected.append({
            "priority": 3,
            "file": item["file"],
            "type": "unknown_regression",
            "old": f"{item['old']} {item['old_time']:.2f}s",
            "new": f"{item['new']} {item['new_time']:.2f}s",
            "category_cluster": item.get("category_cluster", ""),
            "suspected_component": item.get("suspected_component", ""),
            "evidence": item.get("evidence", {}),
        })

    if len(selected) > MAX_ROWS["selected_cases"]:
        selected = selected[:MAX_ROWS["selected_cases"]]
    write_jsonl(output_dir / "selected_cases.jsonl", selected)

    # by_logic.csv  / by_category.csv
    logic_stats = defaultdict(lambda: defaultdict(int))
    cat_stats = defaultdict(lambda: defaultdict(int))
    for r in analysis.get("_records", []):
        logic_stats[r.logic][r.result] += 1
        cat_stats[r.category][r.result] += 1

    write_csv_dicts(
        output_dir / "by_logic.csv",
        [{"logic": k, **dict(v)} for k, v in logic_stats.items()],
        ["logic", "sat", "unsat", "unknown", "timeout", "error", "killed"]
    )
    write_csv_dicts(
        output_dir / "by_category.csv",
        [{"category": k, **dict(v)} for k, v in cat_stats.items()],
        ["category", "sat", "unsat", "unknown", "timeout", "error", "killed"]
    )

    # meta.json
    meta = {
        "run_id": analysis["run_id"],
        "baseline_run_id": analysis["baseline_run_id"],
        "commit": analysis["commit"],
        "timeout_sec": analysis["timeout_sec"],
        "manifest_relation": analysis["manifest_relation"],
        "generated_at": datetime.now().isoformat(),
        "total_files": analysis["total_files"],
        "num_regressions": analysis["num_regressions"],
        "num_solving_improvements": analysis["num_solving_improvements"],
        "num_new_crashes": analysis["num_new_crashes"],
        "num_mismatches": analysis["num_mismatches"],
    }
    with open(output_dir / "meta.json", "w") as f:
        json.dump(meta, f, indent=2)

    # Total size check
    total_size = 0
    for p in output_dir.iterdir():
        if p.is_file():
            total_size += p.stat().st_size

    if total_size > MAX_GIT_PAYLOAD_BYTES:
        print(f"[WARNING] Git payload {total_size} bytes exceeds {MAX_GIT_PAYLOAD_BYTES}. Trimming...")
        # Trim selected_cases and tails
        for p in output_dir.iterdir():
            if p.name == "selected_cases.jsonl":
                with open(p) as f:
                    lines = f.readlines()
                if len(lines) > 20:
                    with open(p, "w") as f:
                        f.writelines(lines[:20])
            if p.suffix == ".md":
                with open(p) as f:
                    text = f.read()
                if len(text) > 50000:
                    with open(p, "w") as f:
                        f.write(text[:50000] + "\n\n... [truncated]\n")

        total_size = sum(p.stat().st_size for p in output_dir.iterdir() if p.is_file())
        print(f"[INFO] Trimmed to {total_size} bytes")

    return total_size


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="NLColver Benchmark Delta Analyzer")
    parser.add_argument("--current", required=True, help="Path to current run directory")
    parser.add_argument("--baseline", default=None, help="Path to baseline run directory")
    parser.add_argument("--z3-baseline", default=None, help="Path to Z3 frozen baseline JSON")
    parser.add_argument("--output", required=True, help="Output directory for analysis artifacts")
    parser.add_argument("--run-id", default="", help="Run identifier")
    parser.add_argument("--baseline-run-id", default="", help="Baseline run identifier")
    parser.add_argument("--commit", default="unknown", help="Git commit hash")
    parser.add_argument("--timeout", type=float, default=30, help="Timeout per case in seconds")
    args = parser.parse_args()

    current_dir = Path(args.current)
    baseline_dir = Path(args.baseline) if args.baseline else None
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)

    current_data = load_statistics(current_dir / "statistics.json")
    baseline_data = load_statistics(baseline_dir / "statistics.json") if baseline_dir else None
    z3_data = load_frozen_baseline(Path(args.z3_baseline)) if args.z3_baseline else None

    # Manifest check
    _, current_manifest = load_manifest(current_dir)
    _, baseline_manifest = load_manifest(baseline_dir) if baseline_dir else (None, None)
    relation = "none"
    if current_manifest and baseline_manifest:
        relation = manifest_relation(current_manifest, baseline_manifest)
    elif current_manifest:
        relation = "current_only"

    if manifest_relation == "invalid":
        print("[WARNING] Baseline manifest mismatch. Delta analysis may be unreliable.")

    records = build_case_records(current_data, baseline_data, z3_data)

    analysis = analyze(records, current_data, baseline_data, relation, args)
    analysis["_records"] = records  # for by_logic / by_category writers

    total_size = enforce_budgets(analysis, output_dir)
    print(f"[Analyze] Written {output_dir} ({total_size} bytes)")


if __name__ == "__main__":
    main()
