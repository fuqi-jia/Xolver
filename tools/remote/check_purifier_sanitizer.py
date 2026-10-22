#!/usr/bin/env python3
"""Compare the archived and fixed Boolean purifier under ASan/UBSan.

Only these small translation units are instrumented. Existing server libraries
are linked under the shared build lock; no second project build tree is made.
This checks the purifier's memory accesses, not all solver/library accesses.
"""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
OLD_CPP = "cbecc918277b846d45b3cf8d2d71ebda51b58e8055563d05713211fbd716f4d6"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    output = ROOT / "validation/native-terms-r5/purifier-sanitizer"
    output.mkdir(parents=True, exist_ok=True)
    baseline = output / "baseline"
    sources = ["src/frontend/preprocess/BoolSubtermPurifier.cpp",
               "src/frontend/preprocess/BoolSubtermPurifier.h"]
    archive = ROOT / "build/native-terms-r1-source.tar.gz"
    with tarfile.open(archive) as snapshot:
        for name in sources:
            target = baseline / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(snapshot.extractfile(name).read())
    if digest(baseline / sources[0]) != OLD_CPP:
        raise SystemExit("archived purifier does not match the recorded pre-fix source")
    records = {}
    # Serializes library readers with incremental build writers.
    with (ROOT / "build/.writer.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        link = shlex.split((ROOT / "build/tests/CMakeFiles/xolver_unit_tests.dir/link.txt").read_text())
        libraries = link[link.index("-o") + 2:]
        libraries = [str(ROOT / "dependencies/native/lib/libgmpxx.a")
                     if item == "-lgmpxx" else item for item in libraries]
        records["libraries"] = {
            str((ROOT / "build/tests" / x).resolve()): digest((ROOT / "build/tests" / x).resolve())
            for x in libraries if x.endswith(".a")
        }
        for label, source in (("baseline", baseline), ("fixed", ROOT)):
            binary = output / (label + "-tests")
            command = ["/usr/bin/c++", "-std=c++17", "-g", "-O1",
                       "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
                       "-I" + str(source / "src"), "-I" + str(ROOT / "src"),
                       "-I" + str(ROOT / "include"),
                       "-I" + str(ROOT / "dependencies/doctest"),
                       str(ROOT / "tests/unit/test_main.cpp"),
                       str(ROOT / "tests/unit/test_bool_subterm_purifier.cpp"),
                       str(source / sources[0]), "-o", str(binary), *libraries]
            (output / (label + "-command.json")).write_text(json.dumps(command, indent=2) + "\n")
            with (output / (label + "-build.log")).open("wb") as log:
                subprocess.run(command, cwd=ROOT / "build/tests", stdout=log,
                               stderr=subprocess.STDOUT, check=True, timeout=180)
            records[label] = {"binary_sha256": digest(binary),
                              "source_sha256": {name: digest(source / name) for name in sources}}
    for label in ("baseline", "fixed"):
        with (output / (label + ".log")).open("wb") as log:
            proc = subprocess.run([str(output / (label + "-tests"))], stdout=log,
                                  stderr=subprocess.STDOUT, timeout=120,
                                  env={**os.environ,
                                       "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1",
                                       "UBSAN_OPTIONS": "halt_on_error=1:print_stacktrace=1"})
        records[label]["rc"] = proc.returncode
    baseline_log = (output / "baseline.log").read_text(errors="replace")
    fixed_log = (output / "fixed.log").read_text(errors="replace")
    metrics = {
        "baseline_use_after_free": int("heap-use-after-free" in baseline_log),
        "fixed_pass": int(records["fixed"]["rc"] == 0 and
                          "AddressSanitizer" not in fixed_log and "runtime error:" not in fixed_log),
    }
    records["metrics"] = metrics
    records["test_sha256"] = digest(ROOT / "tests/unit/test_bool_subterm_purifier.cpp")
    (output / "report.json").write_text(json.dumps(records, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
    print(json.dumps(metrics))
    return int(not all(metrics.values()))


if __name__ == "__main__":
    raise SystemExit(main())
