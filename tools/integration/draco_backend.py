"""Latest Draco 2 model interface backed by a grounder and Xolver ASP.

The grounder is forced into --mode=gringo. Only Xolver performs stable-model
search and optimization. The Draco 2 code and rules are left intact.
"""
from dataclasses import dataclass
import hashlib
import json
import inspect
from pathlib import Path
import re
import shutil
import subprocess
import threading
import types
import time
from typing import Mapping, Sequence


class IncompleteSolve(RuntimeError):
    """An incomplete solve must not become an empty generator/UNSAT result."""


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
    """Latest Draco 2 run_clingo generator seam, with Xolver doing all solving."""
    def __init__(self, draco_module, solver: Path, grounder: SubprocessGrounder,
                 timeout=60.0, evidence: Path = None):
        if timeout <= 0:
            raise ValueError("Draco timeout must be positive")
        if not hasattr(draco_module, "Model"):
            raise TypeError("Draco 2 Model API is required")
        self.draco, self.solver, self.grounder = draco_module, Path(solver).resolve(), grounder
        manifest = json.loads(Path(__file__).with_name("draco-source.json").read_text())
        package_dir = Path(draco_module.__file__).resolve().parent
        checked = {}
        for name in ("run.py", "draco.py", "programs.py", "weights.py", "asp_utils.py", "fact_utils.py"):
            expected = manifest["files"]["draco/"+name]
            actual = digest((package_dir / name).read_bytes())
            if actual != expected:
                raise TypeError("Draco 2 source does not match the frozen runner interface: " + name)
            checked[name] = actual
        self.source_identity = {"repository": manifest["repository"], "revision": manifest["revision"],
                                "module_sha256": checked}
        self.timeout, self.evidence = timeout, Path(evidence) if evidence else None
        self.solver_sha256 = digest(self.solver.read_bytes())
        self.calls = 0
        self._receipts = threading.local()
        self._counter_lock = threading.Lock()

    @staticmethod
    def constants(arguments):
        """Accept grounder constants, never forward foreign solving options."""
        result = {}
        pending = iter(arguments)
        for argument in pending:
            if argument in ("-c", "--const"):
                try:
                    assignment = next(pending)
                except StopIteration as error:
                    raise ValueError("missing ASP constant assignment") from error
            elif argument.startswith("-c "):
                assignment = argument[3:].strip()
            elif argument.startswith("--const="):
                assignment = argument[len("--const="):]
            else:
                raise UnsupportedGrounding("unsupported Draco solver/grounder option: " + argument)
            name, separator, value = assignment.partition("=")
            if not separator:
                raise ValueError("invalid ASP constant assignment")
            result[name] = value
        return result

    @property
    def last_receipt(self):
        return getattr(self._receipts, "value", None)

    def run(self, program, models=0, topK=False, arguments=()):
        import logging
        import clingo  # parse_term is a parser, never Control.solve.
        if not isinstance(models, int) or isinstance(models, bool) or models < 0:
            raise ValueError("model count must be a nonnegative integer")
        if not isinstance(program, str):
            program = "\n".join(program)
        source = program.encode("utf-8")
        constants = self.constants(arguments)
        start = time.monotonic()
        grounded = self.grounder.ground(source, constants, self.timeout)
        ignore = bool(topK and models == 0)
        if ignore:
            logging.warning("Since all models should be computed, topK is ignored.")
            topK = False
        original = grounded.aspif.rstrip()
        if not original.endswith(b"\n0"):
            raise UnsupportedGrounding("missing final ASPIF step terminator")
        prefix = original[:-1]
        has_objective = any(line.startswith(b"2 ") for line in original.splitlines())
        # Explicit #project directives determine classes for non-top-K solving.
        project = []
        explicit_project = False
        for line in original.splitlines():
            if line.startswith(b"3 "):
                fields = list(map(int, line.split()))
                if len(fields) != fields[1]+2:
                    raise UnsupportedGrounding("invalid ASPIF projection directive")
                explicit_project = True
                project.extend(fields[2:])
        blockers = []
        shown_models = set()
        yielded = 0
        while models == 0 or yielded < models:
            remaining = self.timeout - (time.monotonic() - start)
            if remaining <= 0:
                raise IncompleteSolve("Draco budget exhausted during model generation")
            aspif = prefix + b"".join(blockers) + b"0\n"
            command = [str(self.solver), "--timeout-ms", str(max(1, int(remaining * 1000)))]
            if ignore:
                command.append("--opt-mode=ignore")
            solve_start = time.monotonic()
            with self._counter_lock:
                self.calls += 1
                call_id = self.calls
            try:
                solved = subprocess.run(command, input=aspif, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                        timeout=remaining, check=False)
            except subprocess.TimeoutExpired as error:
                solved = subprocess.CompletedProcess(command, 124, error.stdout or b"", error.stderr or b"native deadline exceeded")
            except OSError as error:
                solved = subprocess.CompletedProcess(command, 2, b"", str(error).encode())
            try:
                result = json.loads(solved.stdout)
                if not isinstance(result, dict):
                    raise ValueError("expected a response object")
            except (ValueError, UnicodeDecodeError):
                result = {"Result": "UNKNOWN", "Xolver": {"status": "protocol_error",
                    "reason": "invalid native response: " + solved.stderr.decode(errors="replace")}}
            receipt = {"backend": "xolver-asp", "draco_source": self.source_identity,
                       "program_sha256": digest(source), "constants": constants, "requested_models": models,
                       "blocked_models": len(blockers),
                       "topK": topK, "ignore_objectives": ignore, "grounder": grounded.receipt,
                       "solver": {"command": command, "binary_sha256": self.solver_sha256,
                                  "input_sha256": digest(aspif), "returncode": solved.returncode,
                                  "response_sha256": digest(solved.stdout),
                                  "seconds": time.monotonic() - solve_start},
                       "total_seconds": time.monotonic() - start,
                       "result": result.get("Result"), "evidence": result.get("Xolver")}
            self._receipts.value = receipt
            if self.evidence:
                folder = self.evidence / ("call-{:04d}".format(call_id))
                folder.mkdir(parents=True, exist_ok=False)
                for name, data in (("source.lp", source), ("program.aspif", aspif),
                                   ("grounder.stderr", grounded.diagnostics), ("solver.stdout", solved.stdout),
                                   ("solver.stderr", solved.stderr)):
                    (folder / name).write_bytes(data)
                (folder / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            if solved.returncode or result.get("Result") not in ("SATISFIABLE", "OPTIMUM FOUND", "UNSATISFIABLE"):
                raise IncompleteSolve("Xolver ASP did not decide Draco: " + str(result.get("Xolver", {})))
            if result["Result"] == "UNSATISFIABLE":
                return
            meta = result["Xolver"]
            if not meta.get("stable_model_checked"):
                raise IncompleteSolve("Xolver ASP did not provide a checked stable model")
            chosen = set(meta["true_atoms"])
            universe = project if explicit_project and not topK else meta["atom_ids"]
            literals = [atom if atom in chosen else -atom for atom in sorted(set(universe))]
            # A headless normal rule excludes exactly this complete assignment.
            # Top-K uses every internal atom, including non-shown auxiliaries.
            blockers.append(("1 0 0 0 {} {}\n".format(len(literals), " ".join(map(str, literals)))).encode())
            values = result["Call"][0]["Witnesses"][-1]["Value"]
            projection = tuple(sorted(set(values)))
            if not topK and projection in shown_models:
                continue
            shown_models.add(projection)
            yielded += 1
            costs = [] if ignore else result["Models"].get("Costs", [])
            yield self.draco.Model([clingo.parse_term(value) for value in values], costs, yielded)
            # A proven global optimum is a valid one-element improving stream;
            # heuristic intermediate incumbents are intentionally not exposed.
            if has_objective and not topK and not ignore:
                return

    def is_satisfiable(self, program):
        try:
            next(self.run(program, models=1))
            return True
        except StopIteration:
            return False

    def bind(self, instance):
        """Inject this runner into one Draco 2 instance, leaving modules intact.

        The original methods' code, defaults and closures are retained. Their
        runner globals are private copies, so cached module imports cannot send
        this instance to a different backend and concurrent instances are isolated.
        """
        routes = {"check_spec": ("is_satisfiable", ("self", "spec")),
                  "complete_spec": ("run_clingo", ("self", "spec", "models")),
                  "count_preferences": ("run_clingo", ("self", "spec")),
                  "get_violations": ("run_clingo", ("self", "spec"))}
        bindings = {}
        for name, (route, parameters) in routes.items():
            method = getattr(instance, name)
            function = method.__func__
            if (function.__module__ != self.draco.__package__ + ".draco" or
                tuple(inspect.signature(function).parameters) != parameters or
                route not in function.__code__.co_names or
                any(token in function.__code__.co_names for token in ("Control", "solve"))):
                raise TypeError("the Draco method does not match the frozen runner route: " + name)
            if "run_clingo" not in function.__globals__ or "is_satisfiable" not in function.__globals__:
                raise TypeError("the Draco method does not expose the current runner seam: " + name)
            environment = dict(function.__globals__)
            environment["run_clingo"] = self.run
            environment["is_satisfiable"] = self.is_satisfiable
            injected = types.FunctionType(function.__code__, environment, function.__name__,
                                          function.__defaults__, function.__closure__)
            injected.__kwdefaults__ = function.__kwdefaults__
            injected.__annotations__ = function.__annotations__
            injected.__qualname__ = function.__qualname__
            bindings[name] = types.MethodType(injected, instance)
        for name, method in bindings.items():
            setattr(instance, name, method)
        return instance
