#!/usr/bin/env python3
"""Check source ownership and directed layer boundaries before compiling."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
# Direct dependencies. Search implementations still contain cycles internally;
# they cannot leak into evidence checking, application orchestration or the IR.
LAYERS = {
    "base": [],
    "parallel": ["base"],
    "ir": ["base"],
    "contracts": ["base", "ir"],
    "algebra": ["base", "ir", "contracts"],
    "evidence": ["base", "ir", "contracts"],
    "frontend": ["base", "ir", "contracts", "algebra"],
    "search": ["base", "parallel", "ir", "contracts", "algebra", "evidence"],
    "quantifiers": ["base", "parallel", "ir", "contracts", "algebra", "search"],
    "applications": ["base", "parallel", "ir", "contracts", "algebra", "evidence", "search", "quantifiers"],
    "runtime": ["base", "ir", "contracts", "algebra", "evidence",
                "frontend", "parallel", "search", "quantifiers", "applications"],
}
INCLUDE = re.compile(r'^\s*#\s*include\s*[<"]([^">]+)[">]', re.M)
APPLICATION_CATEGORIES = {
    "satisfiability": {"sat", "smt", "common"},
    "optimization": {"maxsat", "maxsmt", "cp", "milp", "omt", "common"},
    "counting": None,
    "verification": {"pa", "sl", "model_checking", "common"},
    "dynamics": {"ode", "pde", "common"},
}


def inspect(root: Path = ROOT) -> tuple[dict, list[str]]:
    paths = sorted(p for p in (root / "src").rglob("*")
                   if p.suffix in (".cpp", ".h"))
    owned = {p.relative_to(root / "src").as_posix(): p for p in paths}
    errors, edges = [], Counter()
    sources = {layer: [] for layer in LAYERS}
    for name, path in owned.items():
        layer = name.split("/")[0]
        if layer not in LAYERS:
            errors.append(f"unowned source: {name}")
            continue
        if path.suffix == ".cpp":
            sources[layer].append(name)
        text = re.sub(r"/\*.*?\*/|//[^\n]*", "", path.read_text(), flags=re.S)
        if re.search(r"\b(?:CoreIr|CoreExpr)\b", text):
            errors.append(f"retired duplicate expression representation: {name}")
        if name.startswith(("applications/verification/pa/", "quantifiers/integer/")) and re.search(r"\b(?:NativeTerms|TermExpr|Kind|ExprId)\b", text):
            errors.append(f"PA still consumes the general compatibility vocabulary: {name}")
        if name.startswith("applications/"):
            parts = Path(name).parts
            if len(parts) > 2:
                if parts[1] not in APPLICATION_CATEGORIES:
                    errors.append(f"unowned application category: {name}")
                elif len(parts) > 3 and APPLICATION_CATEGORIES[parts[1]] is not None and parts[2] not in APPLICATION_CATEGORIES[parts[1]]:
                    errors.append(f"unowned application family: {name}")
        for include in INCLUDE.findall(text):
            if any(part in (".", "..") for part in include.split("/")):
                errors.append(f"noncanonical include bypasses ownership: {name} -> {include}")
                continue
            if include in owned:
                if name.startswith("applications/") and include.startswith("applications/"):
                    source_parts, target_parts = Path(name).parts, Path(include).parts
                    if len(source_parts) == 2 and len(target_parts) > 2:
                        errors.append(f"application base depends on concrete application: {name} -> {include}")
                    elif len(source_parts) > 2 and len(target_parts) > 2:
                        if source_parts[1] != target_parts[1]:
                            errors.append(f"cross-application dependency: {name} -> {include}")
                        elif source_parts[1] == "verification" and source_parts[2] != target_parts[2] and target_parts[2] != "common":
                            errors.append(f"cross-SV solver dependency: {name} -> {include}")
                        elif source_parts[1:3] == ("satisfiability", "smt") and len(source_parts) > 3 and source_parts[3] == "common" and len(target_parts) > 4 and target_parts[3] != "common":
                            errors.append(f"application common depends on private solver: {name} -> {include}")
                        elif source_parts[2] == "common" and len(target_parts) > 3 and target_parts[2] != "common":
                            errors.append(f"application common depends on private solver: {name} -> {include}")
                target = include.split("/")[0]
                if layer != target:
                    edges[layer, target] += 1
                    if target not in LAYERS[layer]:
                        errors.append(f"forbidden dependency: {name} -> {include}")
            elif include.startswith(tuple(LAYERS) + ("logic/", "decision/", "solvers/", "theory/", "expr/", "util/", "api/", "proof/", "sat/")):
                errors.append(f"missing internal header: {name} -> {include}")
            # Native external solver and parser headers belong to adapters.
            elif ("cadical" in include and layer != "search"
                  or include.startswith("somtparser/frontend/") and layer not in ("frontend", "runtime")
                  or include.startswith("somtparser/passes/") and layer not in ("frontend", "runtime")
                  or include.startswith(("somtparser/ir/", "somtparser/core/")) and layer not in ("ir", "quantifiers", "applications", "frontend", "runtime")
                  or include.startswith(("poly/", "polyxx/")) and layer not in ("algebra", "search", "applications")):
                errors.append(f"external backend leaks into {layer}: {name} -> {include}")
        if layer not in ("base",) and re.search(r"\b(?:getenv|setenv|unsetenv)\s*\(", text):
            errors.append(f"process configuration outside input adapter: {name}")
        if layer != "base" and re.search(r"\benv::(?:get|flag|diag|paramInt|paramLong|paramDouble)\s*\(", text):
            errors.append(f"untyped configuration read: {name}")
    report = {
        "schema": "xolver-architecture/1", "files": len(paths),
        "lines": sum(len(p.read_text().splitlines()) for p in paths),
        "max_directory_depth": max(len(Path(n).parts) - 1 for n in owned),
        "layers": {layer: {"allowed": deps, "sources": sources[layer]}
                   for layer, deps in LAYERS.items()},
        "edges": [{"from": a, "to": b, "includes": n}
                  for (a, b), n in sorted(edges.items())],
        "largest_files": sorted(
            ({"path": n, "lines": len(p.read_text().splitlines())} for n, p in owned.items()),
            key=lambda item: (-item["lines"], item["path"]))[:20],
    }
    return report, errors


def manifest(report: dict) -> str:
    lines = ["# Explicit source ownership; update with architecture.py --write.", ""]
    for name, spec in report["layers"].items():
        lines += [f"set(XOLVER_{name.upper()}_SOURCES"]
        lines += [f'    "{path}"' for path in spec["sources"]]
        lines += [")", ""]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="update explicit source manifest")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report, errors = inspect()
    path = ROOT / "src/sources.cmake"
    expected = manifest(report)
    if args.write and not errors:
        path.write_text(expected)
    elif not path.exists() or path.read_text() != expected:
        errors.append("source ownership differs from src/sources.cmake; review and run --write")
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    for error in errors:
        print(error)
    print(f"{report['files']} source/header files; {len(LAYERS)} layers; {len(errors)} violations")
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
