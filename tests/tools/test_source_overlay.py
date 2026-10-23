"""Source updates must preserve open scripts and reject changed preimages."""
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest

APPLY = Path(__file__).resolve().parents[2] / "tools/remote/apply_overlay.py"
PACKAGE = APPLY.with_name("package_overlay.py")


def archive(root, files, removed=None):
    path = root / "update.tar.gz"
    metadata = {"files": {name: hashlib.sha256(data).hexdigest() for name, data in files.items()},
                "removed": removed or {}}
    entries = {**files, ".xolver-overlay.json": json.dumps(metadata).encode()}
    with tarfile.open(path, "w:gz") as tar:
        for name, data in entries.items():
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o755
            tar.addfile(member, io.BytesIO(data))
    return path


class SourceOverlay(unittest.TestCase):
    def test_committed_project_changes_are_packaged_relative_to_server_base(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            def git(*args):
                return subprocess.check_output(["git", "-c", "user.name=Overlay test",
                    "-c", "user.email=overlay@example.invalid", *args], cwd=root, stderr=subprocess.PIPE)
            git("init", "-q")
            (root / "old.cpp").write_text("server source\n")
            git("add", "."); git("commit", "-qm", "server revision")
            base = git("rev-parse", "HEAD").decode().strip()
            (root / "old.cpp").unlink()
            (root / "new.cpp").write_text("committed feature\n")
            git("add", "-A"); git("commit", "-qm", "feature revision")
            output = root / "update.tar.gz"
            completed = subprocess.run([sys.executable, str(PACKAGE), str(output), "--base", base],
                cwd=root, capture_output=True, text=True, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            record = json.loads(output.with_suffix(".json").read_text())
            self.assertIn("new.cpp", record["members"])
            self.assertEqual(record["removed"]["old.cpp"], hashlib.sha256(b"server source\n").hexdigest())
            self.assertEqual(record["base"], base)
            self.assertNotEqual(record["head"], base)

    def test_committed_submodule_update_is_included_with_exact_removed_preimage(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            dependency, parent = root / "dependency", root / "parent"
            dependency.mkdir(); parent.mkdir()
            def git(cwd, *args):
                return subprocess.check_output(["git", "-c", "user.name=Overlay test",
                    "-c", "user.email=overlay@example.invalid", *args], cwd=cwd, stderr=subprocess.PIPE)
            git(dependency, "init", "-q")
            (dependency / "old.cpp").write_text("old\n")
            git(dependency, "add", "."); git(dependency, "commit", "-qm", "initial")
            git(parent, "init", "-q")
            git(parent, "-c", "protocol.file.allow=always", "submodule", "add", str(dependency), "dep")
            git(parent, "commit", "-qam", "pin dependency")
            sub = parent / "dep"
            (sub / "old.cpp").unlink()
            (sub / "new.cpp").write_text("committed upstream source\n")
            git(sub, "add", "-A"); git(sub, "commit", "-qm", "upstream update")
            output = root / "sources.tar.gz"
            completed = subprocess.run([sys.executable, str(PACKAGE), str(output)], cwd=parent,
                capture_output=True, text=True, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            record = json.loads(output.with_suffix(".json").read_text())
            self.assertIn("dep/new.cpp", record["members"])
            self.assertEqual(record["removed"]["dep/old.cpp"], hashlib.sha256(b"old\n").hexdigest())
            with tarfile.open(output) as tar:
                self.assertEqual(tar.extractfile("dep/new.cpp").read(), b"committed upstream source\n")

    def test_repeated_overlay_preserves_incremental_build_inputs(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            update = archive(root, {"src/Input.cpp": b"int input = 7;\n"})
            command = [sys.executable, str(APPLY), str(update)]
            first = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=10)
            self.assertEqual(first.returncode, 0, first.stderr)
            path = root / "src/Input.cpp"
            os.utime(path, ns=(1_000_000_000, 1_000_000_000))
            before = path.stat()
            second = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=10)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(path.stat().st_ino, before.st_ino)
            self.assertEqual(path.stat().st_mtime_ns, before.st_mtime_ns)
            self.assertEqual(json.loads(second.stdout)["verified_written"], 0)
            self.assertEqual(json.loads(second.stdout)["verified_unchanged"], 1)

    def test_open_reader_keeps_old_script_until_it_finishes(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / "running.sh"
            old, new = b"old script: complete immutable input\n", b"new script: different length\n"
            path.write_bytes(old)
            fd = os.open(path, os.O_RDONLY)
            try:
                self.assertEqual(os.read(fd, 1), old[:1])
                update = archive(root, {"running.sh": new})
                run = subprocess.run([sys.executable, str(APPLY), str(update)],
                                     cwd=root, capture_output=True, text=True, timeout=10)
                self.assertEqual(run.returncode, 0, run.stderr)
                self.assertEqual(os.read(fd, 4096), old[1:])
            finally:
                os.close(fd)
            self.assertEqual(path.read_bytes(), new)
            self.assertEqual(path.stat().st_mode & 0o777, 0o755)

    def test_changed_obsolete_source_aborts_before_any_write(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / "old.cpp"
            path.write_bytes(b"user edit")
            update = archive(root, {"new.cpp": b"replacement"},
                             {"old.cpp": hashlib.sha256(b"expected original").hexdigest()})
            run = subprocess.run([sys.executable, str(APPLY), str(update)],
                                 cwd=root, capture_output=True, text=True, timeout=10)
            self.assertNotEqual(run.returncode, 0)
            self.assertEqual(path.read_bytes(), b"user edit")
            self.assertFalse((root / "new.cpp").exists())
