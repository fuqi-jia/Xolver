#!/usr/bin/env python3
"""Paired, short-timeout validation of one gate removal on the build server.

Keep every attempt, including timeouts and unknowns. Retry changed incomplete
results with a larger bound; never count an incomplete result as a proof.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "fuzz"))
from fuzz_combination_soundness import Gen
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "proof"))
from isabelle_pa import Atom, parse

ANSWER = re.compile(r"^(sat|unsat|unknown)\s*$", re.M)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contradicts(attempt, expected):
    # A timeout or crash cannot retract a verdict already printed. Match each
    # answer to its query; checked_attempt rejects extra or missing answers.
    expected = expected if isinstance(expected, (list, tuple)) else [expected]
    return any(answer in ("sat", "unsat") and oracle in ("sat", "unsat") and answer != oracle
               for answer, oracle in zip(ANSWER.findall(attempt.get("stdout", "")), expected))


def checked_attempt(attempt, queries):
    attempt = dict(attempt)
    answers = ANSWER.findall(attempt.get("stdout", ""))
    attempt["answers"] = answers
    if len(answers) > queries or (attempt["status"] not in ("error", "timeout") and len(answers) != queries):
        attempt.update(status="error", answer_count_error=True)
    elif attempt["status"] not in ("error", "timeout") and "unknown" in answers:
        attempt["status"] = "unknown"
    return attempt


def query_profile(source):
    """Reuse the checked S-expression lexer; count only top-level queries."""
    commands = parse(source)
    count, expected, oracle_commands = 0, None, []
    for command in commands:
        if not isinstance(command, list) or not command or not isinstance(command[0], Atom):
            raise ValueError("invalid SMT-LIB command")
        head = command[0]
        if head.kind != "symbol":
            raise ValueError("quoted command head")
        if head.text in ("check-sat", "check-sat-assuming"):
            count += 1
        if head.text == "set-info" and len(command) == 3:
            key, value = command[1:]
            if isinstance(key, Atom) and key.kind == "symbol" and key.text == ":status":
                expected = (value.text if isinstance(value, Atom) and value.kind == "symbol"
                            and value.text in ("sat", "unsat") else None)
                # The legacy fixture annotation describes its final query.
                # It is not an assumption and must not make an oracle reject
                # earlier incremental answers before it finishes the script.
                continue
        # Xolver accepts empty push/pop as a one-level operation. Oracles
        # receive the explicit standard spelling; candidate input is unchanged.
        if head.text in ("push", "pop") and len(command) == 1:
            command.append(Atom("1"))
        oracle_commands.append(command)

    def render(node):
        pieces, pending = [], [node]
        while pending:
            item = pending.pop()
            if isinstance(item, str):
                pieces.append(item)
            elif isinstance(item, list):
                pieces.append("(")
                pending.append(")")
                for index in range(len(item) - 1, -1, -1):
                    pending.append(item[index])
                    if index:
                        pending.append(" ")
            elif item.kind == "string":
                pieces.append('"' + item.text.replace('"', '""') + '"')
            elif item.kind == "quoted":
                pieces.append("|" + item.text + "|")
            else:
                pieces.append(item.text)
        return "".join(pieces)

    return {"queries": max(count, 1), "expected": expected,
            "oracle_source": "\n".join(render(command) for command in oracle_commands) + "\n"}


def run(command, seconds):
    start = time.monotonic()
    try:
        p = subprocess.run(command, capture_output=True, text=True, timeout=seconds)
        answers = ANSWER.findall(p.stdout)
        result = dict(status=answers[-1] if answers else "error", rc=p.returncode,
                      stdout=p.stdout, stderr=p.stderr)
        if p.returncode:
            result["status"] = "error"
    except subprocess.TimeoutExpired as e:
        def decoded(value):
            return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
        result = dict(status="timeout", rc=None, stdout=decoded(e.stdout), stderr=decoded(e.stderr))
    result.update(seconds=time.monotonic() - start, limit=seconds, command=command)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--solver", required=True, type=Path)
    p.add_argument("--baseline", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--root", default="tests/regression", type=Path)
    p.add_argument("--logics", default="nia,ania,aufnia,ufnia,ufdtnia")
    p.add_argument("--timeout", default=6, type=float)
    p.add_argument("--retry-timeout", default=20, type=float)
    p.add_argument("--generated", default=60, type=int)
    p.add_argument("--seed", default=17001, type=int)
    p.add_argument("--z3", required=True)
    p.add_argument("--cvc5", required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    generated = args.output / "generated"
    generated.mkdir()
    rng = random.Random(args.seed)
    for i in range(args.generated):
        logic = ("QF_ANIA", "QF_AUFNIA", "QF_UFNIA")[i % 3]
        (generated / f"seed-{args.seed}-{i:03d}.smt2").write_text(Gen(rng, logic).formula())
    cases = [(f, False) for logic in args.logics.split(",")
             for f in sorted((args.root / logic).glob("*.smt2"))]
    cases += [(f, True) for f in sorted(generated.glob("*.smt2"))]
    if not cases:
        raise ValueError("empty gate validation")
    counts = Counter(cases=len(cases), wrong_answers=0, errors=0, regressions=0,
                     model_failures=0, model_checks=0, oracle_skips=0,
                     candidate_unknown=0, candidate_timeout=0, baseline_unknown=0,
                     baseline_timeout=0, oracle_checked=0, improved=0)
    records = []
    for index, (path, is_generated) in enumerate(cases):
        row = dict(input=str(path), sha256=digest(path), generated=is_generated)
        profile = query_profile(path.read_text())
        queries, expected = profile["queries"], profile["expected"]
        expected_answers = [None] * (queries - 1) + [expected]
        if is_generated or queries > 1:
            oracle_path = path
            if queries > 1:
                oracle_path = args.output / "oracle-inputs" / (digest(path) + ".smt2")
                oracle_path.parent.mkdir(exist_ok=True)
                oracle_path.write_text(profile["oracle_source"])
                row["oracle_input"] = {"path": str(oracle_path), "sha256": digest(oracle_path)}
            cvc5 = [args.cvc5, "--lang=smt2"] + (["--incremental"] if queries > 1 else [])
            row["oracles"] = [checked_attempt(run([args.z3, str(oracle_path)], args.timeout), queries),
                              checked_attempt(run(cvc5 + [str(oracle_path)], args.timeout), queries)]
            a, b = row["oracles"]
            if (a["status"] in ("sat", "unsat") and b["status"] in ("sat", "unsat")
                    and a["answers"] == b["answers"] and (expected is None or a["answers"][-1] == expected)):
                expected_answers = a["answers"]
                expected = expected_answers[-1]
                counts["oracle_checked"] += 1
            else:
                counts["oracle_skips"] += 1
        row["expected"] = expected
        row["expected_answers"] = expected_answers
        row["queries"] = queries
        for key, solver in (("baseline", args.baseline), ("candidate", args.solver)):
            row[key] = [checked_attempt(run([str(solver), "solve", str(path)], args.timeout), queries)]
        before, after = (row[k][-1]["status"] for k in ("baseline", "candidate"))
        if before != after and after in ("unknown", "timeout"):
            for key, solver in (("baseline", args.baseline), ("candidate", args.solver)):
                row[key].append(checked_attempt(run([str(solver), "solve", str(path)], args.retry_timeout), queries))
        before, after = (row[k][-1]["status"] for k in ("baseline", "candidate"))
        # Check *all* attempts: a later successful retry cannot erase a crash or
        # contradictory answer observed in the original attempt.
        counts["wrong_answers"] += int(any(contradicts(r, expected_answers) for r in row["candidate"]))
        counts["errors"] += int(any(r["status"] == "error" for r in row["candidate"]))
        counts["regressions"] += int(before in ("sat", "unsat") and after not in (before, "error"))
        counts["improved"] += int(before in ("unknown", "timeout") and after == expected)
        for key in ("baseline", "candidate"):
            counts[key + "_" + row[key][-1]["status"]] += 1
        # Check new SAT witnesses and generated SAT cases positively against
        # their original input; unchanged legacy models are outside this audit.
        if after == "sat" and (is_generated or before != "sat"):
            row["model"] = run([str(args.solver), "model-check", str(path)], args.retry_timeout)
            counts["model_checks"] += 1
            counts["model_failures"] += int(row["model"]["status"] != "sat"
                                           or contradicts(row["model"], "sat"))
        records.append(row)
        (args.output / "records.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{index + 1}/{len(cases)} {path.name}: {before} -> {after}", flush=True)
    report = dict(metrics=dict(counts), records=records, seed=args.seed,
                  solver_sha256=digest(args.solver), baseline_sha256=digest(args.baseline))
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(counts)), flush=True)
    return int(any(counts[k] for k in ("wrong_answers", "errors", "regressions", "model_failures", "oracle_skips")))


if __name__ == "__main__":
    raise SystemExit(main())
