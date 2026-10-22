#!/usr/bin/env python3
"""Replay a batch of PA claims in Isabelle, retaining source and theorem hashes."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

import isabelle_pa
import pa_trace
from isabelle_pa import bundle


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def process_identity(pid):
    try:
        # comm can contain spaces and parentheses; fields after its final ')'
        # begin with state (field 3), and starttime is field 22.
        fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return fields[19]
    except (FileNotFoundError, ProcessLookupError):
        return None


def terminate_tree(process):
    """Stop this owned subtree before killing it, including detached sessions."""
    pending, owned = [process.pid], {}
    while pending:
        pid = pending.pop()
        if pid in owned:
            continue
        identity = process_identity(pid)
        if identity is None:
            continue
        try:
            os.kill(pid, signal.SIGSTOP)
        except ProcessLookupError:
            continue
        owned[pid] = identity
        # Java can fork from any of its threads. Once stopped, children cannot
        # be hidden by a parent spawning new work during recursive discovery.
        for task in Path(f"/proc/{pid}/task").glob("*"):
            try:
                pending.extend(int(child) for child in (task / "children").read_text().split())
            except (FileNotFoundError, ProcessLookupError):
                pass
    for pid, identity in reversed(list(owned.items())):
        if process_identity(pid) == identity:  # Never target a reused PID.
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    process.wait()


def replay(claims: list[dict], isabelle: Path, output: Path, cache: Path, timeout=600):
    if not claims:
        raise ValueError("empty proof batch")
    isabelle = isabelle.resolve(strict=True)
    output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(__file__, output / "replay_driver.py")
    shutil.copyfile(isabelle_pa.__file__, output / "translator.py")
    shutil.copyfile(pa_trace.__file__, output / "certificate_translator.py")
    records = []
    for i, claim in enumerate(claims):
        source_path = Path(claim["input"])
        name = f"PA_Case_{i:04}"
        path = output / name
        certificate_path = Path(claim["certificate"]) if "certificate" in claim else None
        certificate = pa_trace.load(certificate_path.read_text()) if certificate_path else None
        record = bundle(source_path.read_text(), claim["verdict"], path, claim.get("model"), name, certificate)
        if certificate_path:
            record.update(original_certificate_path=str(certificate_path.resolve()),
                          original_certificate_sha256=sha(certificate_path))
        record.update(name=name, original_path=str(source_path.resolve()),
                      original_sha256=sha(source_path))
        records.append(record)
    # One shared session and heap cache; only small theorem/source bundles are
    # archived per experiment. Serialize all writers to that session.
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / ".writer.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        project = cache / "current"
        project.mkdir(exist_ok=True)
        home = cache / "user"
        settings = home / ".isabelle" / "Isabelle2025-2" / "etc" / "settings"
        settings.parent.mkdir(parents=True, exist_ok=True)
        settings.write_text(
            'ISABELLE_JAVA_SYSTEM_OPTIONS="-server -Dfile.encoding=UTF-8 '
            '-Disabelle.threads=2 -XX:+UseSerialGC"\n'
            'ISABELLE_TOOL_JAVA_OPTIONS="-Djava.awt.headless=true -Xms128m -Xmx1g '
            '-Xss4m -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=512m '
            '-XX:ActiveProcessorCount=2 -XX:+UseSerialGC -XX:-CreateCoredumpOnCrash"\n'
            'ML_OPTIONS="--minheap 128 --maxheap 2048"\n')
        shutil.copyfile(settings, output / "isabelle-settings.txt")
        for record in records:
            name = record["name"]
            shutil.copyfile(output / name / f"{name}.thy", project / f"{name}.thy")
        root = ('session Xolver_PA = HOL +\n'
                '  options [document = false, quick_and_dirty = false]\n'
                '  theories\n' + "".join("    " + r["name"] + "\n" for r in records))
        (project / "ROOT").write_text(root)
        (output / "ROOT.batch").write_text(root)
        command = [str(isabelle), "build", "-v", "-D", str(project.resolve()),
                   "-o", "threads=2", "-o", "parallel_proofs=0", "-o", "quick_and_dirty=false"]
        env = dict(os.environ, USER_HOME=str(home.resolve()))
        version = subprocess.run([str(isabelle), "version"], env=env, capture_output=True,
                                 text=True, timeout=30, check=True).stdout.strip()
        if version != "Isabelle2025-2":
            raise RuntimeError("this driver requires the pinned Isabelle2025-2 release")
        start = time.monotonic()
        with (output / "isabelle.log").open("w") as log:
            process = subprocess.Popen(command, env=env, stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                rc = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                terminate_tree(process)
                rc = 124
        # Do not label changed or partially generated artifacts as verified.
        for record in records:
            name = record["name"]
            if ("certificate_sha256" in record and
                    sha(output / name / "certificate.json") != record["certificate_sha256"]):
                raise RuntimeError("certificate changed while checking")
            if (sha(project / f"{name}.thy") != record["theory_sha256"] or
                    sha(output / name / f"{name}.thy") != record["theory_sha256"] or
                    sha(output / name / "input.smt2") != record["input_sha256"]):
                raise RuntimeError("proof inputs changed while checking")
        verified = rc == 0
        for record in records:
            record["status"] = "kernel-checked" if verified else "unverified"
            (output / record["name"] / "claim.json").write_text(json.dumps(record, indent=2) + "\n")
        report = {
            "schema": "xolver-pa-replay/1", "verified": verified, "returncode": rc,
            "seconds": time.monotonic() - start, "command": command,
            "isabelle_release": version, "settings_sha256": sha(settings),
            "checker_driver_sha256": sha(__file__),
            "log_sha256": sha(output / "isabelle.log"), "claims": records,
            "trust_boundary": "SMT-LIB translation is not formally verified; no C++ refinement",
        }
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True,
                        help="JSON array of input paths, verdicts and optional models")
    parser.add_argument("--isabelle", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=600)
    args = parser.parse_args()
    report = replay(json.loads(args.manifest.read_text()), args.isabelle,
                    args.output, args.cache, args.timeout)
    print(json.dumps({k: v for k, v in report.items() if k != "claims"}))
    return 0 if report["verified"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
