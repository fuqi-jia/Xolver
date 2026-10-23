#!/usr/bin/env python3
"""Package changed working-tree files, optionally relative to a prior manifest."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("output", type=Path)
    p.add_argument("--since", type=Path)
    p.add_argument("--base", default="HEAD", help="source revision already present on the server")
    args = p.parse_args()
    base = subprocess.check_output(["git", "rev-parse", "--verify", args.base + "^{commit}"]).decode().strip()
    before = json.loads(args.since.read_text())["files"] if args.since else {}
    names = set()
    for command in (["git", "diff", base, "--name-only", "-z"],
                    ["git", "ls-files", "--others", "--exclude-standard", "-z"]):
        names.update(subprocess.check_output(command).decode().split("\0"))
    # A previous overlay can contain a file since restored to HEAD. Include
    # that restoration even though git diff no longer lists the path.
    names.update(before)
    # A gitlink alone does not contain working-tree edits inside a submodule.
    # Preserve those exact files and their base revisions in the overlay.
    submodules = {}
    removed = {}
    module_states = subprocess.check_output(["git", "submodule", "status"]).decode().splitlines()
    module_roots = [line.strip(" +-U").split()[1] + "/" for line in module_states]
    migration = Path("docs/audit/architecture-migration.json")
    moves = json.loads(migration.read_text())["moves"] if migration.exists() else []
    move_preimages = {move["from"]: move["before_sha256"] for move in moves}
    # Ordinary deletions (including formerly untracked overlay members) must
    # reach the server too. A source-move list alone misses retired tests and
    # helpers, leaving stale code in recursive builds.
    deleted = set(filter(None, subprocess.check_output([
        "git", "diff", base, "--name-only", "--diff-filter=D", "-z"
    ]).decode().split("\0")))
    deleted.update(name for name in before if not Path(name).exists())
    for name in sorted(deleted):
        if name.startswith("docs/audit/evidence/") or any(name.startswith(p) for p in module_roots):
            continue
        removed[name] = before.get(name) or move_preimages.get(name) or hashlib.sha256(
            subprocess.check_output(["git", "show", base + ":" + name])).hexdigest()
    for line in module_states:
        revision, directory, *_ = line.strip(" +-U").split()
        submodules[directory] = revision
        # The dependency can now contain committed upstream/PR changes. Diff
        # against the superproject's pin, not just its dirty working tree.
        pinned = subprocess.check_output(["git", "rev-parse", base + ":" + directory]).decode().strip()
        for command in (["git", "-C", directory, "diff", pinned, "--name-only", "-z"],
                        ["git", "-C", directory, "ls-files", "--others", "--exclude-standard", "-z"]):
            names.update(directory + "/" + n for n in subprocess.check_output(command).decode().split("\0") if n)
        deleted = subprocess.check_output([
            "git", "-C", directory, "diff", pinned, "--name-only", "--diff-filter=D", "-z"
        ]).decode().split("\0")
        for name in filter(None, deleted):
            path = directory + "/" + name
            removed[path] = before.get(path) or hashlib.sha256(subprocess.check_output([
                "git", "-C", directory, "show", pinned + ":" + name
            ])).hexdigest()
    # Evidence is deliberately excluded. Filter it before filesystem probes:
    # repeated stat calls over archived suites are expensive on WSL/DrvFS.
    paths = sorted(n for n in names if n and not n.startswith("docs/audit/evidence/")
                   and Path(n).is_file())
    hashes = {n: hashlib.sha256(Path(n).read_bytes()).hexdigest() for n in paths}
    changed = [n for n in paths if before.get(n) != hashes[n]]
    # Source moves carry exact preimages. An overlay must remove the obsolete
    # paths as well as add replacements, or a recursive build can compile both.
    for move in moves:
        if not Path(move["from"]).exists() and Path(move["to"]).is_file():
            removed.setdefault(move["from"], move["before_sha256"])
    with tarfile.open(args.output, "w:gz") as archive:
        for name in changed:
            archive.add(name, arcname=name)
        metadata = json.dumps({"files": {n: hashes[n] for n in changed},
                               "removed": removed}).encode()
        entry = tarfile.TarInfo(".xolver-overlay.json")
        entry.size = len(metadata)
        archive.addfile(entry, io.BytesIO(metadata))
    record = {"base": base, "head": subprocess.check_output(["git", "rev-parse", "HEAD"]).decode().strip(),
              "archive_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
              "delta_from": str(args.since) if args.since else None,
              "members": changed, "files": hashes, "removed": removed,
              "submodules": submodules}
    args.output.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{len(changed)} files, {args.output.stat().st_size} bytes: {args.output}")


if __name__ == "__main__":
    main()
