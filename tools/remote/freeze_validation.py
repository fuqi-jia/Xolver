#!/usr/bin/env python3
"""Freeze test inputs/drivers while holding the shared source/build writer lock."""
import argparse
import hashlib
import json
from pathlib import Path
import stat


DIRECTORIES = ("tools", "tests/tools", "tests/regression", "tests/known_gaps", "tests/integration")


def freeze(root: Path, output: Path):
    output.mkdir(parents=True, exist_ok=False)
    records = {}
    for directory in DIRECTORIES:
        for path in sorted((root / directory).rglob("*")):
            if not path.is_file() or "__pycache__" in path.parts or path.suffix == ".pyc":
                continue
            if path.is_symlink():
                raise ValueError(f"validation input must be a regular file: {path}")
            relative = path.relative_to(root).as_posix()
            content = path.read_bytes()
            target = output / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
            mode = stat.S_IMODE(path.stat().st_mode)
            target.chmod(mode)
            records[relative] = dict(sha256=hashlib.sha256(content).hexdigest(),
                                     bytes=len(content), mode=mode)
    (output / "manifest.json").write_text(json.dumps(records, indent=2) + "\n")
    return records


def verify(output: Path):
    records = json.loads((output / "manifest.json").read_text())
    for relative, record in records.items():
        path = output / relative
        if (path.is_symlink() or not path.is_file() or
                hashlib.sha256(path.read_bytes()).hexdigest() != record["sha256"] or
                stat.S_IMODE(path.stat().st_mode) != record["mode"]):
            raise ValueError(f"frozen validation input changed: {relative}")
    return len(records)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    count = verify(args.output) if args.verify else len(freeze(args.root, args.output))
    print(f"{count} validation input/driver files {'verified' if args.verify else 'frozen'}")
