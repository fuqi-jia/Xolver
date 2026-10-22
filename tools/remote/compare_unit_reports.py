#!/usr/bin/env python3
"""Compare complete doctest JUnit reports while retaining known failures."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET


def read_report(path: Path, exit_code: int, minimum_cases: int):
    if exit_code not in (0, 1):
        raise ValueError(f"unit process did not complete: exit {exit_code}")
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    # doctest writes its declaration at start and the result tree at run end.
    # Legacy tests can print diagnostics between them. Keep the raw file intact;
    # only parse the unique complete final report, never a truncated prefix.
    roots = list(re.finditer(r"(?m)^<testsuites(?:\s|>)", text))
    if len(roots) != 1:
        raise ValueError("expected one complete doctest testsuites report")
    document = ET.fromstring(text[roots[0].start():])
    cases = document.findall(".//testcase")
    identities = Counter((case.get("classname", ""), case.get("name", "")) for case in cases)
    if len(cases) < minimum_cases or any(not key[1] for key in identities):
        raise ValueError(f"incomplete unit case inventory: {len(cases)}")
    failures = Counter()
    for case in cases:
        key = (case.get("classname", ""), case.get("name", ""))
        if case.find("skipped") is not None or case.get("status", "run") != "run":
            raise ValueError("unit case was not run")
        count = len(case.findall("failure")) + len(case.findall("error"))
        if count:
            failures[key] += count
    if (exit_code == 0) != (not failures):
        raise ValueError("unit exit status disagrees with reported failures")
    # doctest's tests attribute counts assertions, not testcase elements.
    suites = document.findall(".//testsuite")
    reported = sum(int(s.get("failures", "0")) + int(s.get("errors", "0")) for s in suites)
    if reported != sum(failures.values()):
        raise ValueError("unit failure totals disagree with testcase results")
    summary = {"sha256": hashlib.sha256(raw).hexdigest(), "exit_code": exit_code,
               "cases_including_subcases": len(cases),
               "assertions": sum(int(s.get("tests", "0")) for s in suites),
               "diagnostic_prefix_bytes": len(text[:roots[0].start()].encode("utf-8")),
               "failures": [{"test": list(key), "count": count} for key, count in sorted(failures.items())]}
    return summary, identities, failures


def compare(baseline: Path, candidate: Path, baseline_exit: int, candidate_exit: int,
            minimum_cases: int = 1600):
    before, before_ids, before_failures = read_report(baseline, baseline_exit, minimum_cases)
    after, after_ids, after_failures = read_report(candidate, candidate_exit, minimum_cases)
    if before_ids != after_ids:
        raise ValueError("unit case identities or multiplicities changed")
    new = {key: count for key, count in after_failures.items() if count > before_failures.get(key, 0)}
    return {"baseline": before, "candidate": after,
            "metrics": {"full_units_complete": 1, "new_unit_failures": len(new)},
            "new_failures": [{"test": list(key), "count": count} for key, count in sorted(new.items())]}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline", required=True, type=Path)
    p.add_argument("--candidate", required=True, type=Path)
    p.add_argument("--baseline-exit", required=True, type=int)
    p.add_argument("--candidate-exit", required=True, type=int)
    p.add_argument("--minimum-cases", type=int, default=1600)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    try:
        result = compare(args.baseline, args.candidate, args.baseline_exit, args.candidate_exit,
                         args.minimum_cases)
    except (ValueError, ET.ParseError, OSError) as error:
        result = {"error": str(error), "metrics": {"full_units_complete": 0, "new_unit_failures": -1}}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["metrics"]))
    return int(not result["metrics"]["full_units_complete"] or result["metrics"]["new_unit_failures"] != 0)


if __name__ == "__main__":
    raise SystemExit(main())
