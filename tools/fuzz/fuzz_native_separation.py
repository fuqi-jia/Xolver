#!/usr/bin/env python3
"""Replay the frozen SL corpus through the real parser/CLI and pin exported heaps."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

from fuzz_presburger import invoke

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "proof"))
from isabelle_pa import Atom, parse  # one shared, quoted-symbol-aware SMT reader


def emit(node):
    if isinstance(node, list):
        return "(" + " ".join(emit(child) for child in node) + ")"
    if not isinstance(node, Atom) or node.kind == "string":
        raise ValueError("unexpected model string")
    return "|" + node.text + "|" if node.kind == "quoted" else node.text


def pins(output):
    expressions = parse(output)
    if len(expressions) != 3 or emit(expressions[0]) != "sat":
        raise ValueError("expected a SAT result, bindings and a heap")
    bindings, heap = expressions[1:]
    if not isinstance(bindings, list) or not isinstance(heap, list) or len(heap) != 3:
        raise ValueError("malformed heap model")
    if emit(heap[0]) != "heap" or not isinstance(heap[2], list) or len(heap[2]) != 3:
        raise ValueError("missing heap/nil interpretation")
    if emit(heap[2][0]) != "=" or emit(heap[2][1]) != "(as sep.nil Int)":
        raise ValueError("unexpected nil interpretation")
    assertions, names = [], set()
    for binding in bindings:
        if (not isinstance(binding, list) or len(binding) != 5
                or emit(binding[0]) != "define-fun" or binding[2] != []
                or emit(binding[3]) not in ("Int", "Bool")):
            raise ValueError("unsupported model binding")
        name = emit(binding[1])
        if name in names:
            raise ValueError("duplicate model binding")
        names.add(name)
        assertions.append(f"(assert (= {name} {emit(binding[4])}))")
    assertions.extend("(assert " + emit(term) + ")" for term in heap[1:])
    return "\n".join(assertions) + "\n"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solver", "cvc5", "corpus", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    for source in (Path(__file__).resolve(), Path(__file__).resolve().with_name("fuzz_presburger.py"),
                   Path(__file__).resolve().parents[1] / "proof/isabelle_pa.py",
                   Path(__file__).resolve().parents[1] / "proof/pa_trace.py"):
        relative = source.relative_to(Path(__file__).resolve().parents[1])
        target = args.output / "driver/tools" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    cases = json.loads((args.corpus / "candidate.json").read_text())
    counts = dict(cases=0, library_disagreements=0, oracle_disagreements=0,
                  unknown=0, errors=0, timeouts=0, oracle_skips=0, models=0,
                  malformed_models=0, model_rejections=0, model_skips=0)
    records = []
    for index, case in enumerate(cases):
        original = args.corpus / case["input"]
        source = original.read_text()
        # This driver consumes the generated single-query corpus only.
        if source.count("(check-sat)") != 1:
            raise ValueError("expected one generated check-sat command")
        prefix = source.replace("(check-sat)", "")
        query = args.output / f"case-{index:04}.smt2"
        query.write_text(prefix + "(check-sat)(get-model)\n")
        candidate = invoke([str(args.solver), "solve", str(query), "--check-model"], args.timeout)
        oracle = invoke([str(args.cvc5), "--lang=smt2", str(original)], args.timeout)
        verdict = candidate["result"]
        counts["cases"] += 1
        for result, name in (("unknown", "unknown"), ("error", "errors"), ("timeout", "timeouts")):
            counts[name] += verdict == result
        counts["library_disagreements"] += (
            verdict in ("sat", "unsat") and case["result"] in ("sat", "unsat")
            and verdict != case["result"])
        if oracle["result"] not in ("sat", "unsat"):
            counts["oracle_skips"] += 1
        else:
            counts["oracle_disagreements"] += verdict in ("sat", "unsat") and verdict != oracle["result"]
        row = dict(index=index, input_sha256=sha(original), query_sha256=sha(query),
                   library=case["result"], candidate=candidate, oracle=oracle)
        if verdict == "sat":
            counts["models"] += 1
            try:
                pinned = args.output / f"pinned-{index:04}.smt2"
                pinned.write_text(prefix + pins(candidate["stdout"]) + "(check-sat)\n")
            except ValueError as error:
                counts["malformed_models"] += 1
                row["model_error"] = str(error)
            else:
                checked = invoke([str(args.cvc5), "--lang=smt2", str(pinned)], args.timeout)
                counts["model_rejections"] += checked["result"] == "unsat"
                counts["model_skips"] += checked["result"] not in ("sat", "unsat")
                row.update(model=checked, pinned_sha256=sha(pinned))
            if "MODEL_MISMATCH" in candidate.get("stderr", ""):
                counts["model_rejections"] += 1
        records.append(row)
        (args.output / "progress.json").write_text(json.dumps(counts) + "\n")
    report = dict(metrics=counts, records=records, solver_sha256=sha(args.solver),
                  oracle_sha256=sha(args.cvc5), corpus_sha256=sha(args.corpus / "candidate.json"))
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    (args.output / "metrics.json").write_text(json.dumps(counts) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return int(counts["cases"] != 240 or not counts["models"] or
               any(value for key, value in counts.items() if key not in ("cases", "models")))


if __name__ == "__main__":
    raise SystemExit(main())
