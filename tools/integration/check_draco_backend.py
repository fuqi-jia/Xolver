#!/usr/bin/env python3
"""Run the pinned original Draco API with Xolver, then an independent clingo."""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import subprocess
import sys
import time

from draco_backend import DracoBackend, SubprocessGrounder, UnsupportedGrounding
from check_asp_backend import clingo, replay

PINNED = "607e9134b3749210fe13b33248bf139a22d7b787"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--draco", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--clingo", nargs="+", required=True)
    parser.add_argument("--grounder-artifact", type=Path, action="append", default=[])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    revision = subprocess.check_output(["git", "-C", str(args.draco), "rev-parse", "HEAD"]).decode().strip()
    if revision != PINNED:
        raise ValueError("Draco source does not match the frozen integration revision")
    expected = json.loads((Path(__file__).parent / "draco-source.json").read_text())
    for name, checksum in expected["files"].items():
        if hashlib.sha256((args.draco / name).read_bytes()).hexdigest() != checksum:
            raise ValueError("Draco source changed: " + name)
    sys.path.insert(0, str(args.draco.resolve()))
    module = importlib.import_module("draco.run")
    package = importlib.import_module("draco")
    grounder = SubprocessGrounder(args.clingo, args.grounder_artifact)
    backend = DracoBackend(module, args.solver, grounder, args.timeout, args.output / "xolver")
    cases = [("valid", 0), ("invalid", 0), ("strip", 0), ("scatter", 0), ("histogram", 1)]
    records = []
    with backend.attach():
        for name, extra in cases:
            query = (args.draco / "asp/examples" / (name + ".lp")).read_text().splitlines()
            constants = {"max_extra_encs": str(extra)}
            started = time.monotonic()
            # Execute the original Draco.run and its original Result parser.
            answer = module.run(query, constants=constants, silence_warnings=True)
            api_seconds = time.monotonic()-started
            receipt = backend.last_receipt
            folder = args.output / "xolver" / ("call-{:04d}".format(backend.calls))
            source = (folder / "source.lp").read_bytes()
            grounded = (folder / "program.aspif").read_bytes()
            native = json.loads((folder / "solver.stdout").read_bytes())
            command = [*args.clingo, "--outf=2", "--quiet=1,2,2", "-c", "max_extra_encs="+str(extra)]
            reference = subprocess.run(command, input=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       timeout=args.timeout)
            (folder / "reference.stdout").write_bytes(reference.stdout)
            (folder / "reference.stderr").write_bytes(reference.stderr)
            independent = json.loads(reference.stdout)
            if independent["Result"] != native["Result"]:
                raise AssertionError((name, independent["Result"], native["Result"]))
            if native["Result"] == "UNSATISFIABLE":
                if answer is not None:
                    raise AssertionError("Draco Result parser did not preserve infeasibility")
            else:
                if answer is None:
                    raise AssertionError("Draco Result parser lost a valid model")
                if independent["Models"].get("Costs", []) != native["Models"].get("Costs", []):
                    raise AssertionError((name, "different exact costs"))
                checked = replay(grounded, native, args.clingo, args.timeout)
                (folder / "replay.json").write_text(json.dumps(checked, indent=2)+"\n")
                if native["Result"] == "OPTIMUM FOUND" and answer.cost != native["Models"]["Costs"][0]:
                    raise AssertionError("Draco Result cost was not preserved")
            records.append({"name": name, "constants": constants, "result": native["Result"],
                            "cost": None if answer is None else answer.cost,
                            "api_seconds": api_seconds, "independently_verified": True,
                            "receipt": receipt})
        # The public helper binds run_clingo at import time; it must use the
        # adapter as well, rather than silently reaching the original solver.
        before = backend.calls
        valid = (args.draco / "asp/examples/valid.lp").read_text().splitlines()
        invalid = (args.draco / "asp/examples/invalid.lp").read_text().splitlines()
        if not package.is_valid(valid) or package.is_valid(invalid):
            raise AssertionError("Draco is_valid helper returned the wrong verdict")
        if backend.calls != before+2:
            raise AssertionError("Draco helper bypassed the Xolver backend")
    duplicate_source = b"a. #minimize { 3,x:a; 3,x:a; 3,y:a }.\n"
    duplicate = grounder.ground(duplicate_source, {}, args.timeout)
    duplicate_process = subprocess.run([str(args.solver)], input=duplicate.aspif,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=args.timeout)
    duplicate_result = json.loads(duplicate_process.stdout)
    if duplicate_result.get("Result") != "OPTIMUM FOUND" or duplicate_result["Models"]["Costs"] != [6]:
        raise AssertionError("source objective tuples were not deduplicated by the grounder")
    (args.output / "tuple-deduplication.json").write_text(json.dumps({"source": duplicate_source.decode(),
        "grounder": duplicate.receipt, "result": duplicate_result}, indent=2)+"\n")
    try:
        grounder.ground(b"{a}. #minimize { #inf,a: a }.\n", {}, args.timeout)
    except UnsupportedGrounding as error:
        infinite = {"result": "unsupported", "reason": str(error)}
    else:
        raise AssertionError("a non-integer objective tuple was silently discarded")
    report = {"draco_revision": revision, "grounder_version": grounder.version,
              "grounder_artifacts": grounder.artifacts, "solver_sha256": backend.solver_sha256,
              "programs": len(records), "draco_api_calls": backend.calls,
              "independently_verified": sum(r["independently_verified"] for r in records),
              "infinite_objective_boundary": infinite, "records": records,
              "performance_superiority_claimed": False}
    (args.output / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ("records", "grounder_version")}))


if __name__ == "__main__":
    main()
