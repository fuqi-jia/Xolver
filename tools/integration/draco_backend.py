"""Draco's original run_clingo interface backed by a grounder and Xolver ASP.

The grounder is forced into --mode=gringo. Only Xolver performs stable-model
search and optimization. The original Draco code and rules are left intact.
"""
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Mapping, Sequence, Tuple


class IncompleteSolve(RuntimeError):
    """An incomplete solve must not become Draco's None/UNSAT result."""


class UnsupportedGrounding(RuntimeError):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class Grounded:
    aspif: bytes
    diagnostics: bytes
    receipt: dict


class SubprocessGrounder:
    def __init__(self, command: Sequence[str], artifacts: Sequence[Path] = (), max_bytes=64 * 1024 * 1024):
        if isinstance(command, (str, bytes)) or not command:
            raise TypeError("grounder command must be an argument sequence")
        self.command, self.max_bytes = tuple(command), max_bytes
        resolved = shutil.which(self.command[0])
        if not resolved:
            raise FileNotFoundError(self.command[0])
        files = [Path(resolved).resolve(), *map(Path, artifacts)]
        self.artifacts = {str(path): digest(path.read_bytes()) for path in files}
        version = subprocess.run([*self.command, "--version"], stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, timeout=15, check=True)
        self.version = version.stdout.decode("utf-8", errors="replace")

    def ground(self, source: bytes, constants: Mapping[str, str], timeout: float, silence_warnings=False):
        command = [*self.command, "--mode=gringo", "--output=intermediate"]
        if silence_warnings:
            command.append("--warn=no-atom-undefined")
        for name, value in sorted(constants.items()):
            if not re.fullmatch(r"[a-z][A-Za-z0-9_]*", name):
                raise ValueError("invalid ASP constant name")
            command.extend(("-c", name + "=" + str(value)))
        start = time.monotonic()
        result = subprocess.run(command, input=source, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        if result.returncode:
            raise UnsupportedGrounding(result.stderr.decode("utf-8", errors="replace"))
        if len(result.stdout) > self.max_bytes or not result.stdout.startswith(b"asp 1 0 0"):
            raise UnsupportedGrounding("grounder did not produce a supported bounded ASPIF message")
        # In particular, non-integer #inf weights must not silently disappear
        # while an optimality result is claimed for the source objective.
        if b"tuple ignored" in result.stderr.lower():
            raise UnsupportedGrounding("grounder ignored an objective tuple: " +
                                       result.stderr.decode("utf-8", errors="replace"))
        receipt = {"role": "ground-only", "command": command, "version": self.version,
                   "artifacts": self.artifacts, "source_sha256": digest(source),
                   "aspif_sha256": digest(result.stdout), "diagnostics_sha256": digest(result.stderr),
                   "seconds": time.monotonic() - start}
        return Grounded(result.stdout, result.stderr, receipt)


class DracoBackend:
    def __init__(self, draco_module, solver: Path, grounder: SubprocessGrounder,
                 timeout=60.0, evidence: Path = None):
        if timeout <= 0:
            raise ValueError("Draco timeout must be positive")
        self.draco, self.solver, self.grounder = draco_module, Path(solver).resolve(), grounder
        self.timeout, self.evidence = timeout, Path(evidence) if evidence else None
        self.solver_sha256 = digest(self.solver.read_bytes())
        self.calls = 0
        self.last_receipt = None

    def run_clingo(self, draco_query, constants=None, files=None, relax_hard=False,
                   silence_warnings=False, debug=False) -> Tuple[bytes, bytes]:
        start = time.monotonic()
        selected = list(files or self.draco.DRACO_LP)
        if relax_hard:
            selected = [name for name in selected if name != "hard-integrity.lp"]
        sources = []
        identities = {}
        for name in selected:
            path = Path(self.draco.DRACO_LP_DIR) / name
            data = path.read_bytes()
            sources.append(data)
            identities[name] = digest(data)
        query = "\n".join(draco_query).encode("utf-8")
        source = b"\n".join([*sources, query])
        grounded = self.grounder.ground(source, constants or {}, self.timeout, silence_warnings)
        remaining = self.timeout - (time.monotonic() - start)
        if remaining <= 0:
            raise IncompleteSolve("Draco budget exhausted during grounding")
        command = [str(self.solver), "--timeout-ms", str(max(1, int(remaining * 1000)))]
        solve_start = time.monotonic()
        solved = subprocess.run(command, input=grounded.aspif, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=remaining, check=False)
        try:
            result = json.loads(solved.stdout)
        except (ValueError, UnicodeDecodeError) as error:
            raise IncompleteSolve("invalid Xolver ASP response: " + solved.stderr.decode(errors="replace")) from error
        receipt = {"input_sha256": digest(query), "rule_files": identities,
                   "constants": dict(constants or {}), "relax_hard": relax_hard,
                   "grounder": grounded.receipt,
                   "solver": {"command": command, "binary_sha256": self.solver_sha256,
                              "input_sha256": digest(grounded.aspif), "returncode": solved.returncode,
                              "response_sha256": digest(solved.stdout),
                              "seconds": time.monotonic() - solve_start},
                   "total_seconds": time.monotonic() - start,
                   "result": result.get("Result"), "evidence": result.get("Xolver")}
        self.calls += 1
        self.last_receipt = receipt
        if self.evidence:
            folder = self.evidence / ("call-{:04d}".format(self.calls))
            folder.mkdir(parents=True, exist_ok=False)
            for name, data in (("source.lp", source), ("program.aspif", grounded.aspif),
                               ("grounder.stderr", grounded.diagnostics), ("solver.stdout", solved.stdout),
                               ("solver.stderr", solved.stderr)):
                (folder / name).write_bytes(data)
            (folder / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        if solved.returncode or result.get("Result") not in ("SATISFIABLE", "OPTIMUM FOUND", "UNSATISFIABLE"):
            raise IncompleteSolve("Xolver ASP did not decide Draco: " + str(result.get("Xolver", {})))
        return grounded.diagnostics + solved.stderr, solved.stdout

    @contextmanager
    def attach(self):
        """Temporarily replace the original module's documented backend seam.

        The original Draco run() and Result parser still execute. Use separate
        module/process instances for concurrent adapters; this seam is global.
        """
        modules = [self.draco]
        package = getattr(self.draco, "__package__", "")
        for name in (package, package + ".helper"):
            module = sys.modules.get(name)
            if module is not None and module not in modules and hasattr(module, "run_clingo"):
                modules.append(module)
        previous = [(module, module.run_clingo) for module in modules]
        for module in modules:
            module.run_clingo = self.run_clingo
        try:
            yield self.draco
        finally:
            for module, callback in previous:
                module.run_clingo = callback
