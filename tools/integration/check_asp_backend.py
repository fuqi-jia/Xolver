#!/usr/bin/env python3
"""Independent small ASP checks; full clingo is an explicit test-only oracle."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile


def write_program(rules, objectives=()):
    lines = ["asp 1 0 0"]
    for choice, heads, body, threshold in rules:
        prefix = [1, int(choice), len(heads), *heads]
        if threshold is None:
            line = prefix + [0, len(body), *[literal for literal, _ in body]]
        else:
            line = prefix + [1, threshold, len(body)]
            for literal, weight in body:
                line += [literal, weight]
        lines.append(" ".join(map(str, line)))
    for priority, terms in objectives:
        line = [2, priority, len(terms)]
        for literal, weight in terms:
            line += [literal, weight]
        lines.append(" ".join(map(str, line)))
    for atom in range(1, 5):
        label = "a" + str(atom)
        lines.append("4 {} {} 1 {}".format(len(label), label, atom))
    return ("\n".join([*lines, "0"]) + "\n").encode()


def clingo(command, source, timeout):
    process = subprocess.run([*command, "--mode=clasp", "--outf=2", "--quiet=1,2,2"], input=source,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if process.returncode not in (0, 10, 20, 30):
        raise RuntimeError(process.stderr.decode(errors="replace"))
    return json.loads(process.stdout)


def replay(source, result, command, timeout):
    meta = result["Xolver"]
    if not meta["stable_model_checked"]:
        raise AssertionError("native witness was not checked")
    chosen = set(meta["true_atoms"])
    assumptions = [atom if atom in chosen else -atom for atom in meta["atom_ids"]]
    # Force the entire internal model. An independent ASP engine checks
    # stability of the same original ASPIF, not merely visible output atoms.
    data = source.rstrip()
    if not data.endswith(b"\n0"):
        raise AssertionError("missing ASPIF terminator")
    data = data[:-1] + ("6 {} {}\n0\n".format(len(assumptions), " ".join(map(str, assumptions)))).encode()
    checked = clingo(command, data, timeout)
    if checked["Result"] not in ("SATISFIABLE", "OPTIMUM FOUND"):
        raise AssertionError("independent ASP witness replay failed")
    return checked


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--clingo", nargs="+", help="full solver command, used only as independent reference")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args()
    temporary = tempfile.TemporaryDirectory(prefix="xolver-asp-") if args.output is None else None
    if temporary:
        args.output = Path(temporary.name) / "checks"
    args.output.mkdir(parents=True, exist_ok=False)
    generator = random.Random(385714)
    cases = [
        ([(False, [1], [(2, 1)], None), (False, [2], [(1, 1)], None), (False, [], [(-1, 1)], None)], []),
        ([(True, [1, 2, 3, 4], [], None)], [(3, [(1, -2), (2, 1)]), (-2, [(3, -5), (4, 3)])]),
    ]
    for index in range(args.count):
        rules = []
        for _ in range(generator.randrange(1, 9)):
            choice = generator.randrange(4) == 0
            heads = generator.sample(range(1, 5), generator.randrange(3) if choice else generator.randrange(2))
            weighted = generator.randrange(2) == 0
            body = [(generator.choice((-1, 1))*generator.randrange(1, 5),
                     generator.randrange(4) if weighted else 1) for _ in range(generator.randrange(5))]
            rules.append((choice, heads, body, generator.randrange(6) if weighted else None))
        objectives = []
        if index % 2:
            objectives = [(priority, [(generator.choice((-1, 1))*generator.randrange(1, 5),
                                      generator.randrange(-5, 7)) for _ in range(5)]) for priority in (7, -2)]
        cases.append((rules, objectives))
    records = []
    for index, (rules, objectives) in enumerate(cases):
        folder = args.output / ("case-{:04d}".format(index))
        folder.mkdir()
        source = write_program(rules, objectives)
        (folder / "program.aspif").write_bytes(source)
        process = subprocess.run([str(args.solver), "--timeout-ms", str(int(args.timeout*1000))], input=source,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=args.timeout+1)
        (folder / "xolver.stdout").write_bytes(process.stdout)
        (folder / "xolver.stderr").write_bytes(process.stderr)
        native = json.loads(process.stdout)
        if process.returncode or native["Result"] == "UNKNOWN":
            raise AssertionError((index, native))
        record = {"input_sha256": hashlib.sha256(source).hexdigest(), "result": native["Result"],
                  "verified": False, "unfounded_cuts": native["Xolver"]["unfounded_cuts"]}
        if args.clingo:
            independent = clingo(args.clingo, source, args.timeout)
            (folder / "clingo.json").write_text(json.dumps(independent, indent=2)+"\n")
            if independent["Result"] != native["Result"]:
                raise AssertionError((index, independent["Result"], native["Result"]))
            if native["Result"] != "UNSATISFIABLE":
                if independent.get("Models", {}).get("Costs", []) != native.get("Models", {}).get("Costs", []):
                    raise AssertionError((index, "different optima"))
                checked = replay(source, native, args.clingo, args.timeout)
                (folder / "replay.json").write_text(json.dumps(checked, indent=2)+"\n")
            record["verified"] = True
        records.append(record)
    summary = {"cases": len(records), "independently_verified": sum(r["verified"] for r in records),
               "solver_sha256": hashlib.sha256(args.solver.read_bytes()).hexdigest(), "records": records}
    (args.output / "report.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({k:v for k,v in summary.items() if k != "records"}))


if __name__ == "__main__":
    main()
