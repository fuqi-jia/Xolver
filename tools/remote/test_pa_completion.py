#!/usr/bin/env python3
"""Server-only PA coverage/CRT audit with actual certificates and pinned models.

Schema checks are not proof checking. Run test_pa_certificates.py separately for
Isabelle replay. Every fixture, output, model pin and executable hash is retained.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "proof"))
from pa_trace import load, obligations
from test_pa_certificates import model
from isabelle_pa import Atom, parse


def numeral(x):
    return str(x) if x >= 0 else f"(- {-x})"


def portable_oracle_source(source):
    """Use d | t iff mod(t,d)=0; keep the candidate's indexed input unchanged.

    The server Z3 rejects indexed divisible, and its cvc5 version parses indices
    through uint64_t. Both accept arbitrary-precision positive integer moduli.
    Retain every lowered oracle input and hash alongside the original formula.
    """
    def render(node):
        if isinstance(node, Atom):
            if node.kind == "quoted":
                return "|" + node.text + "|"
            if node.kind == "string":
                return '"' + node.text.replace('"', '""') + '"'
            return node.text
        if (node and isinstance(node[0], list) and
                node[0][:2] == [Atom("_"), Atom("divisible")]):
            if (len(node) != 2 or len(node[0]) != 3 or
                    not isinstance(node[0][2], Atom) or node[0][2].kind != "symbol" or
                    not node[0][2].text.isdecimal() or int(node[0][2].text) <= 0):
                raise ValueError("invalid indexed divisibility in oracle input")
            return "(= (mod " + render(node[1]) + " " + node[0][2].text + ") 0)"
        return "(" + " ".join(map(render, node)) + ")"
    return "\n".join(map(render, parse(source))) + "\n"


def fixtures():
    for name, body, expected in [
        ("indexed-all", "(assert (forall ((x Int)) ((_ divisible 1000003) (* 1000003 x))))", "sat"),
        ("indexed-not-all", "(assert (forall ((x Int)) ((_ divisible 2) x)))", "unsat"),
        ("nary-div-identity", "(assert (forall ((x Int)) (= (div x 2 2) (div (div x 2) 2))))", "sat"),
        ("signed-nary-div", "(assert (forall ((x Int)) (= (div x (- 3) (- 2)) (div (div x (- 3)) (- 2)))))", "sat"),
        ("nary-div-model", "(declare-const x Int)(assert (= (div x 2 2) 3))(assert (= (mod x 2) 1))", "sat"),
        ("large-mod-model", "(declare-const x Int)(assert (= (mod x 1000003) 123456))", "sat"),
        ("coprime-model", "(declare-const x Int)(assert (= (mod x 1000003) 123456))(assert (= (mod x 1000033) 654321))", "sat"),
        ("noncoprime-conflict", "(assert (exists ((x Int)) (and (= (mod x 6000018) 2) (= (mod x 4000012) 1))))", "unsat"),
        ("noncoprime-model", "(declare-const x Int)(assert (= (mod x 6000018) 2))(assert (= (mod x 4000012) 2))", "sat"),
        ("negative-coefficient", "(declare-const x Int)(assert (= (mod (* (- 6) x) 1000003) 17))", "sat"),
        ("negative-large-model", "(declare-const x Int)(assert (= (mod x 1000003) 17))(assert (not ((_ divisible 3) x)))"
         "(assert (< x (- 1000000000000000000000000000000)))", "sat"),
        ("below-first-residue", "(declare-const x Int)(assert (= (mod x 1000003) 17))(assert (<= 0 x))(assert (< x 17))", "unsat"),
        ("first-residue-endpoint", "(declare-const x Int)(assert (= (mod x 1000003) 17))(assert (<= 0 x))(assert (<= x 17))", "sat"),
        ("large-exclusions", "(declare-const x Int)(assert (not ((_ divisible 1000000000000000000000000000003) x)))"
         "(assert (not ((_ divisible 1000000000000000000000000000033) (+ x 1))))", "sat"),
        ("excluded-cover", "(assert (exists ((x Int)) (and (not ((_ divisible 2) x))"
         "(not ((_ divisible 4) (+ x 1))) (not ((_ divisible 4) (+ x 3))))))", "unsat"),
        ("excluded-short-interval", "(declare-const x Int)(assert (not ((_ divisible 2) x)))"
         "(assert (not ((_ divisible 4) (+ x 1))))(assert (<= (- 3) x))(assert (< x 0))", "sat"),
    ]:
        yield name, body, expected, 32 if "div" in name else 1
    magnitude = 123456789012345678901234567890123456789012345678901234567890123456789
    divisors = (1000003, -1000033, 1000037)
    for sign in (-1, 1):
        value = sign * magnitude
        quotient = value
        for divisor in divisors:
            quotient //= abs(divisor)
            if divisor < 0:
                quotient = -quotient
        expression = "(div x " + " ".join(map(numeral, divisors)) + ")"
        yield f"nary-huge-{sign}", f"(declare-const x Int)(assert (= x {numeral(value)}))" + \
            f"(assert (= {expression} {numeral(quotient)}))", "sat", 1
    yield "nested-nary-key", "(declare-const x Int)(assert (= x 80))" + \
        "(assert (= (div (div x 2 2) 4) 5))", "sat", 32
    rng = random.Random(20261022)
    for i in range(96):
        lower = rng.randint(-30, 0)
        upper = lower + rng.randint(0, 30)
        conditions = [(rng.choice([-3, -2, -1, 1, 2, 3]), rng.randint(-8, 8),
                       rng.randint(2, 13), rng.choice([False, True])) for _ in range(4)]
        predicates = []
        for a, b, modulus, negated in conditions:
            atom = f"((_ divisible {modulus}) (+ (* {numeral(a)} x) {numeral(b)}))"
            predicates.append(f"(not {atom})" if negated else atom)
        conjunction = "(and " + " ".join(predicates) + ")"
        domain = f"(and (<= {numeral(lower)} x) (<= x {numeral(upper)}))"
        values = [all(((a * x + b) % modulus == 0) != negated
                      for a, b, modulus, negated in conditions) for x in range(lower, upper + 1)]
        if i % 3 == 0:
            body = f"(assert (forall ((x Int)) (=> {domain} {conjunction})))"
            holds = all(values)
        elif i % 3 == 1:
            body = f"(assert (exists ((x Int)) (and {domain} {conjunction})))"
            holds = any(values)
        else:
            body = f"(declare-const x Int)(assert (and {domain} {conjunction}))"
            holds = any(values)
        yield f"bounded-{i:03}", body, "sat" if holds else "unsat", 1


def invoke(command, seconds, env=None):
    start = time.monotonic()
    try:
        run = subprocess.run(command, capture_output=True, text=True, timeout=seconds, env=env)
        answers = [x.strip() for x in run.stdout.splitlines() if x.strip() in ("sat", "unsat", "unknown")]
        # An unknown certificate request may exit nonzero because it cannot
        # publish completed evidence; preserve both verdict and return status.
        result = answers[0] if len(answers) == 1 else "error"
        return dict(result=result, rc=run.returncode, stdout=run.stdout, stderr=run.stderr,
                    seconds=time.monotonic()-start, command=command)
    except subprocess.TimeoutExpired as error:
        def text(data):
            return data.decode(errors="replace") if isinstance(data, bytes) else data or ""
        return dict(result="timeout", stdout=text(error.stdout), stderr=text(error.stderr),
                    seconds=time.monotonic()-start, command=command)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solver", "z3", "cvc5", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--timeout", type=float, default=6)
    parser.add_argument("--include-nary-div", action="store_true", help="Requires the upstream SOMTParser n-ary div fix")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(__file__, args.output / "driver.py")
    dependencies = args.output / "driver-dependencies"
    dependencies.mkdir()
    for name in ("pa_trace", "isabelle_pa", "test_pa_certificates", "replay_pa", "test_pa_isabelle"):
        module = sys.modules[name]
        shutil.copyfile(module.__file__, dependencies / Path(module.__file__).name)
    counts = dict(cases=0, correct=0, wrong=0, errors=0, unknown=0, timeouts=0,
                  certificates=0, model_checks=0, bad_models=0, model_incomplete=0, oracle_checks=0,
                  oracle_errors=0, baseline_unknown=0, baseline_wrong=0)
    rows = []
    pending = []
    for name, body, expected, residues in fixtures():
        if not args.include_nary_div and ("nary" in name or name == "signed-nary-div"):
            pending.append(dict(name=name, reason="upstream SOMTParser n-ary div text parsing pending; native API tested separately"))
            continue
        source = "(set-logic LIA)\n" + body + "\n(check-sat)\n"
        path = args.output / (name + ".smt2")
        path.write_text(source)
        oracle_path = args.output / (name + ".oracle.smt2")
        oracle_path.write_text(portable_oracle_source(source))
        env = {**os.environ, "XOLVER_PA_WORK": "300000", "XOLVER_PA_RESIDUES": str(residues)}
        observations = {}
        for label, executable in (("candidate", args.solver), ("baseline", args.baseline)):
            if executable is None:
                continue
            certificate = args.output / (name + "." + label + ".json")
            observations[label] = invoke([str(executable), "solve", str(path),
                "--produce-pa-certificate", str(certificate), "--produce-models"], args.timeout, env)
            if label == "baseline":
                counts["baseline_unknown"] += observations[label]["result"] == "unknown"
                counts["baseline_wrong"] += observations[label]["result"] in ("sat", "unsat") and observations[label]["result"] != expected
        candidate = observations["candidate"]
        counts["cases"] += 1
        counts["unknown"] += candidate["result"] == "unknown"
        counts["timeouts"] += candidate["result"] == "timeout"
        counts["errors"] += candidate["result"] == "error" or (candidate["result"] in ("sat", "unsat") and candidate.get("rc") != 0)
        counts["wrong"] += candidate["result"] in ("sat", "unsat") and candidate["result"] != expected
        if candidate["result"] == expected and candidate.get("rc") == 0:
            counts["correct"] += 1
            try:
                trace = load((args.output / (name + ".candidate.json")).read_text())
                obligations(trace, expected)
                counts["certificates"] += 1
                candidate["qe_steps"] = len(trace["steps"])
            except (ValueError, OSError) as error:
                candidate["certificate_error"] = str(error)
                counts["errors"] += 1
        commands = {"z3": [str(args.z3), "-smt2"], "cvc5": [str(args.cvc5), "--lang=smt2"]}
        for oracle, command in commands.items():
            observations[oracle] = invoke(command + [str(oracle_path)], args.timeout)
            passed = observations[oracle]["result"] == expected and observations[oracle].get("rc") == 0
            counts["oracle_checks"] += passed
            counts["oracle_errors"] += not passed
        if candidate["result"] == "sat":
            try:
                bindings = model(source, candidate["stdout"])
                if bindings is not None:
                    pinned = args.output / (name + ".pinned.smt2")
                    constraints = "".join(f"(assert (= {key} {str(value).lower() if type(value) is bool else numeral(value)}))\n"
                                          for key, value in bindings.items())
                    original_pin = args.output / (name + ".pinned-indexed.smt2")
                    original_pin.write_text("(set-logic LIA)\n" + body + constraints + "(check-sat)\n")
                    pinned.write_text(portable_oracle_source(original_pin.read_text()))
                    checks = {key: invoke(command + [str(pinned)], args.timeout) for key, command in commands.items()}
                    observations["model_checks"] = checks
                    if all(row["result"] == "sat" and row.get("rc") == 0 for row in checks.values()):
                        counts["model_checks"] += 1
                    elif any(row["result"] == "unsat" and row.get("rc") == 0 for row in checks.values()):
                        counts["bad_models"] += 1
                    else:
                        counts["model_incomplete"] += 1
            except ValueError as error:
                candidate["model_error"] = str(error)
                counts["bad_models"] += 1
        rows.append(dict(name=name, input=path.name, input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                         oracle_input=oracle_path.name, oracle_input_sha256=hashlib.sha256(oracle_path.read_bytes()).hexdigest(),
                         expected=expected, residues=residues, observations=observations))
        (args.output / "progress.json").write_text(json.dumps(counts) + "\n")
    binaries = {name: dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                for name, path in (("solver", args.solver), ("baseline", args.baseline), ("z3", args.z3), ("cvc5", args.cvc5)) if path}
    counts["passed"] = int(counts["cases"] == counts["correct"] == counts["certificates"] and
                           counts["oracle_checks"] == 2 * counts["cases"] and counts["model_checks"] > 0 and
                           not any(counts[k] for k in ("wrong", "errors", "unknown", "timeouts", "bad_models", "model_incomplete", "oracle_errors")))
    (args.output / "report.json").write_text(json.dumps(dict(metrics=counts, binaries=binaries, records=rows, pending_parser_cases=pending), indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return not counts["passed"]


if __name__ == "__main__":
    raise SystemExit(main())
