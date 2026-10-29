#!/usr/bin/env python3
"""Validate the frozen latest Draco 2 API using Xolver and independent Clingo."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib
import json
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

from draco_backend import DracoBackend, SubprocessGrounder, UnsupportedGrounding
from check_asp_backend import clingo, replay

PINNED = "580047a9b5a41b153b24059275e8050b36c38658"


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
        raise ValueError("Draco 2 source does not match the frozen latest revision")
    expected = json.loads((Path(__file__).parent / "draco-source.json").read_text())
    for name, checksum in expected["files"].items():
        if hashlib.sha256((args.draco / name).read_bytes()).hexdigest() != checksum:
            raise ValueError("Draco 2 source changed: " + name)
    sys.path.insert(0, str(args.draco.resolve()))
    import clingo as clingo_library
    records = []
    # Cover import-time default instances, the public constructor, backend
    # construction, binding and every native method with the no-solve guard.
    with patch.object(clingo_library.Control, "solve", side_effect=AssertionError("external solve in Xolver path")):
        module = importlib.import_module("draco.run")
        package = importlib.import_module("draco")
        original_runner = module.run_clingo
        grounder = SubprocessGrounder(args.clingo, args.grounder_artifact)
        backend = DracoBackend(module, args.solver, grounder, args.timeout, args.output / "xolver")
        native = backend.bind(package.Draco())
        valid_dict = {"field": [{"name": "temperature", "type": "number"}],
                      "mark": [{"type": "tick", "encoding": [{"channel": "x", "field": "temperature"}]}],
                      "scale": [{"channel": "x", "type": "linear"}]}
        invalid_dict = {**valid_dict, "mark": [{"type": "tickk", "encoding": [{"channel": "x", "field": "temperature"}]}]}
        valid, invalid = package.dict_to_facts(valid_dict), package.dict_to_facts(invalid_dict)
        before = backend.calls
        if not native.check_spec(valid) or native.check_spec(invalid):
            raise AssertionError("Draco 2 check_spec returned an incorrect verdict")
        if backend.calls != before+2:
            raise AssertionError("check_spec bypassed the Xolver runner")
        if native.get_violations(invalid) != ["invalid_domain"]:
            raise AssertionError("Draco 2 violation extraction failed")
        if native.count_preferences("") != {}:
            raise AssertionError("Draco 2 preference extraction failed")
        for name in ("scatter", "histogram", "binned_histogram"):
            query = (args.draco / "draco/asp/examples" / (name+".lp")).read_text()
            first = backend.calls
            models = list(native.complete_spec(query, models=1))
            if len(models) != 1 or not isinstance(models[0], module.Model) or models[0].number != 1:
                raise AssertionError((name, "Draco 2 Model interface was not preserved"))
            structured = package.answer_set_to_dict(models[0].answer_set)
            records.append({"name": name, "input_sha256": hashlib.sha256(query.encode()).hexdigest(),
                            "cost": models[0].cost, "structured": structured,
                            "native_calls": list(range(first+1, backend.calls+1))})
        topk = list(backend.run("2 {a(1..5)}. :- not a(2). #minimize {1,X:a(X)}.", models=10, topK=True))
        if [model.cost for model in topk] != [[2]]*4+[[3]]*6:
            raise AssertionError("top-K cost tiers are incorrect")
        if len({tuple(sorted(map(str, model.answer_set))) for model in topk}) != 10:
            raise AssertionError("top-K lost distinct full stable models")
        all_models = list(backend.run("{a;b;c}.", models=0))
        if len(all_models) != 8:
            raise AssertionError("finite model enumeration is incomplete")
        ignored = list(backend.run("{a;b}. #minimize {1:a;2:b}.", models=0, topK=True))
        if len(ignored) != 4 or any(model.cost for model in ignored):
            raise AssertionError("topK=all did not preserve objective-ignore semantics")
        for value in (1, 2, 5):
            model = next(backend.run("#const foo=0. a(1..foo).", models=1, arguments=["-c foo="+str(value)]))
            if len(list(model.answer_set)) != value:
                raise AssertionError("packed Draco 2 constant arguments were not preserved")
        duplicate = next(backend.run("a. #minimize {3,x:a;3,x:a;3,y:a}.", models=1, topK=True))
        if duplicate.cost != [6]:
            raise AssertionError("source objective tuple deduplication is incorrect")
    if module.run_clingo is not original_runner or package.run_clingo is not original_runner:
        raise AssertionError("instance injection mutated module runner bindings")
    # An unbound Clingo instance and a bound Xolver instance may coexist.
    external = package.Draco()
    before = backend.calls
    with ThreadPoolExecutor(max_workers=2) as pool:
        xolver_future = pool.submit(native.check_spec, valid)
        clingo_future = pool.submit(external.check_spec, invalid)
        if not xolver_future.result() or clingo_future.result():
            raise AssertionError("concurrent backend instances crossed wires")
    if backend.calls != before+1:
        raise AssertionError("concurrent backend identity was not isolated")
    try:
        grounder.ground(b"{a}. #minimize {#inf,a:a}.\n", {}, args.timeout)
    except UnsupportedGrounding as error:
        infinite = {"result": "unsupported", "reason": str(error)}
    else:
        raise AssertionError("non-integer objective tuples were silently discarded")
    verified = []
    for folder in sorted((args.output / "xolver").glob("call-*")):
        receipt = json.loads((folder / "receipt.json").read_text())
        source = (folder / "source.lp").read_bytes()
        aspif = (folder / "program.aspif").read_bytes()
        result = json.loads((folder / "solver.stdout").read_bytes())
        independent = clingo(args.clingo, aspif, args.timeout)
        (folder / "independent.json").write_text(json.dumps(independent, indent=2)+"\n")
        if result["Result"] == "UNSATISFIABLE":
            if independent["Result"] != "UNSATISFIABLE":
                raise AssertionError((str(folder), "opposite verdict"))
        else:
            checked = replay(aspif, result, args.clingo, args.timeout)
            (folder / "replay.json").write_text(json.dumps(checked, indent=2)+"\n")
            if result["Models"].get("Costs", []) != checked["Models"].get("Costs", []):
                raise AssertionError((str(folder), "witness cost mismatch"))
            if result["Result"] == "OPTIMUM FOUND" and result["Models"].get("Costs", []) != independent["Models"].get("Costs", []):
                raise AssertionError((str(folder), "incorrect optimum"))
        # The first solve for a source also receives a fresh independent
        # source-to-Clingo check, rather than trusting only the shared ASPIF.
        if receipt["blocked_models"] == 0:
            command = [*args.clingo, "--outf=2", "--quiet=1,2,2"]
            if receipt["ignore_objectives"]:
                command.append("--opt-mode=ignore")
            for name, value in sorted(receipt["constants"].items()):
                command += ["-c", name+"="+str(value)]
            reference = subprocess.run(command, input=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       timeout=args.timeout)
            (folder / "source-reference.stdout").write_bytes(reference.stdout)
            (folder / "source-reference.stderr").write_bytes(reference.stderr)
            reference_result = json.loads(reference.stdout)
            if (reference_result["Result"] == "UNSATISFIABLE") != (result["Result"] == "UNSATISFIABLE"):
                raise AssertionError((str(folder), "source-level opposite verdict"))
            if result["Result"] == "OPTIMUM FOUND" and result["Models"].get("Costs", []) != reference_result["Models"].get("Costs", []):
                raise AssertionError((str(folder), "source-level optimum mismatch"))
        verified.append({"receipt": str(folder.relative_to(args.output)), "result": result["Result"],
                         "cost": result["Models"].get("Costs", []), "independently_verified": True})
    if not backend.calls or len(verified) != backend.calls:
        raise AssertionError("not every real Xolver invocation was independently checked")
    report = {"draco_repository": expected["repository"], "draco_revision": revision,
              "draco_version": package.__version__, "grounder_version": grounder.version,
              "grounder_artifacts": grounder.artifacts, "solver_sha256": backend.solver_sha256,
              "programs": len(records), "native_invocations": backend.calls,
              "independently_verified": len(verified), "infinite_objective_boundary": infinite,
              "records": records, "verified_calls": verified,
              "performance_superiority_claimed": False}
    (args.output / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ("records", "verified_calls", "grounder_version")}))


if __name__ == "__main__":
    main()
