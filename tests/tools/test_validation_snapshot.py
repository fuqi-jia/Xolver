import importlib.util
from pathlib import Path
import tempfile
import unittest
import os
import shutil
import subprocess
import sys

from test_source_overlay import archive

SCRIPT = Path(__file__).resolve().parents[2] / "tools/remote/freeze_validation.py"
SPEC = importlib.util.spec_from_file_location("freeze_validation", SCRIPT)
FREEZE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FREEZE)


class ValidationSnapshot(unittest.TestCase):
    def test_overlay_and_configure_share_the_writer_lock_and_keep_failed_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            remote = root / "tools/remote"
            remote.mkdir(parents=True)
            for name in ("validate.sh", "apply_overlay.py"):
                shutil.copyfile(SCRIPT.parent / name, remote / name)
            update = archive(root, {"src/Input.cpp": b"new source"})
            commands = root / "commands"
            commands.mkdir()
            cmake = commands / "cmake"
            cmake.write_text(f"#!{sys.executable}\n" + '''
import fcntl
from pathlib import Path
assert Path("src/Input.cpp").read_bytes() == b"new source"
with Path("build/.writer.lock").open("w") as writer:
    try:
        fcntl.flock(writer, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("source applied; writer lock held")
        raise SystemExit(23)
raise SystemExit("configure ran outside the writer lock")
''')
            cmake.chmod(0o755)
            env = dict(os.environ, PATH=str(commands) + os.pathsep + os.environ["PATH"])
            command = ["bash", str(remote / "validate.sh"), "atomic", str(update)]
            run = subprocess.run(command, env=env, capture_output=True, text=True, timeout=10)
            self.assertEqual(run.returncode, 23, run.stdout + run.stderr)
            log = root / "validation/atomic/configure.log"
            self.assertEqual(log.read_text(), "source applied; writer lock held\n")
            # A retry must not truncate the original failure's records.
            retry = subprocess.run(command, env=env, capture_output=True, text=True, timeout=10)
            self.assertNotEqual(retry.returncode, 0)
            self.assertEqual(log.read_text(), "source applied; writer lock held\n")

    def test_checkout_changes_cannot_change_running_validation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "source"
            case = root / "tests/regression/example.smt2"
            case.parent.mkdir(parents=True)
            case.write_text("(assert false)")
            driver = root / "tools/runner.sh"
            driver.parent.mkdir()
            driver.write_text("#!/bin/sh\nexit 0\n")
            driver.chmod(0o755)
            output = Path(temporary) / "inputs"
            FREEZE.freeze(root, output)
            case.write_text("(assert true)")
            driver.unlink()
            self.assertEqual(FREEZE.verify(output), 2)
            self.assertEqual((output / "tests/regression/example.smt2").read_text(), "(assert false)")
            with self.assertRaises(FileExistsError):
                FREEZE.freeze(root, output)
            (output / "tests/regression/example.smt2").write_text("(assert true)")
            with self.assertRaisesRegex(ValueError, "changed"):
                FREEZE.verify(output)
