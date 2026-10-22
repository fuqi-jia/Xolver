from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/proof"))
try:
    import replay_pa
finally:
    sys.path.pop(0)


class ProofProcessCleanup(unittest.TestCase):
    def test_detached_proof_child_does_not_survive_timeout_cleanup(self):
        with tempfile.TemporaryDirectory() as folder:
            marker = Path(folder) / "child"
            script = """import os,pathlib,subprocess,sys,time
p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'],start_new_session=True)
pathlib.Path(sys.argv[1]).write_text(str(p.pid))
time.sleep(60)
"""
            process = subprocess.Popen([sys.executable, "-c", script, str(marker)],
                                       start_new_session=True)
            try:
                deadline = time.monotonic() + 5
                while not marker.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(marker.exists())
                child = int(marker.read_text())
                replay_pa.terminate_tree(process)
                deadline = time.monotonic() + 2
                while time.monotonic() < deadline:
                    try:
                        state = Path(f"/proc/{child}/stat").read_text().rsplit(")", 1)[1].split()[0]
                    except (FileNotFoundError, ProcessLookupError):
                        state = "gone"
                    if state in {"gone", "Z"}:
                        break
                    time.sleep(0.01)
                self.assertIn(state, {"gone", "Z"})
            finally:
                if process.poll() is None:
                    replay_pa.terminate_tree(process)


if __name__ == "__main__":
    unittest.main()
