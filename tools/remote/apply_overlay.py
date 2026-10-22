#!/usr/bin/env python3
"""Apply a hash-checked source overlay under the caller's build writer lock."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys
import tarfile
import tempfile

root = Path.cwd().resolve()
archive = Path(sys.argv[1])


def local(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError(f"unsafe overlay path: {name}")
    result = root.joinpath(*path.parts)
    if not result.resolve().is_relative_to(root):
        raise ValueError(f"overlay leaves checkout: {name}")
    return result


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


with tarfile.open(archive) as tar:
    metadata = json.load(tar.extractfile(".xolver-overlay.json"))
    members = {member.name: member for member in tar.getmembers()}
    for name, sha in metadata["files"].items():
        local(name)
        if not members[name].isfile():
            raise ValueError(f"non-regular source member: {name}")
        if hashlib.sha256(tar.extractfile(name).read()).hexdigest() != sha:
            raise ValueError(f"corrupt source member: {name}")
    obsolete = {}
    for name, sha in metadata["removed"].items():
        path = local(name)
        if path.exists():
            if path.is_symlink() or digest(path) != sha:
                raise ValueError(f"obsolete source changed since migration: {name}")
            obsolete[name] = sha
    # Archive and verify every preimage before removing any obsolete path.
    if obsolete:
        stamp = hashlib.sha256(archive.read_bytes()).hexdigest()[:16]
        backup = root / "validation" / f"migration-preimages-{stamp}.tar.gz"
        backup.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(backup, "w:gz") as saved:
            for name in obsolete:
                saved.add(local(name), arcname=name)
        with tarfile.open(backup) as saved:
            for name, sha in obsolete.items():
                assert hashlib.sha256(saved.extractfile(name).read()).hexdigest() == sha
        backup.with_suffix(".sha256").write_text(digest(backup) + "\n")
    unchanged = 0
    for name, sha in metadata["files"].items():
        path = local(name)
        if (path.is_file() and not path.is_symlink() and digest(path) == sha
                and path.stat().st_mode & 0o777 == members[name].mode & 0o777):
            # Preserve mtimes and inodes for the persistent incremental build.
            unchanged += 1
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        # Bash can keep reading a script after a long child process finishes.
        # Replacing the inode preserves its open descriptor; truncating the
        # running script in place can splice versions and produce syntax errors.
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".xolver-overlay-",
                                             delete=False) as output:
                temporary = Path(output.name)
                output.write(tar.extractfile(name).read())
                output.flush()
                os.fsync(output.fileno())
                os.fchmod(output.fileno(), members[name].mode & 0o777)
            os.replace(temporary, path)
            temporary = None
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    for name in obsolete:
        local(name).unlink()
    for path in sorted((root / "src").rglob("*"), key=lambda p: len(p.parts), reverse=True):
        if path.is_dir() and not any(path.iterdir()):
            path.rmdir()
print(json.dumps({"verified_written": len(metadata["files"]) - unchanged,
                  "verified_unchanged": unchanged,
                  "archived_removed": len(obsolete), "archive_sha256": digest(archive)}))
