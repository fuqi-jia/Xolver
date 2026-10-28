import subprocess
import os
import signal
import sys
import tempfile
from pathlib import Path
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.process_budget import run_with_budget


class ArithmeticProcessBudget(unittest.TestCase):
    @staticmethod
    def output(process):
        def spawn(*args, **kwargs):
            kwargs['stdout'].write(b'sat\n')
            kwargs['stdout'].flush()
            return process
        return spawn

    def test_slow_process_creation_consumes_the_existing_budget(self):
        process = Mock(pid=17, returncode=0)
        with patch('tools.process_budget.subprocess.Popen', side_effect=self.output(process)), \
                patch('tools.process_budget.time.monotonic', side_effect=[0, 55, 58]):
            stdout, _, timing = run_with_budget(['solver'], 60, {})
        process.wait.assert_called_once_with(timeout=5)
        process.communicate.assert_not_called()
        self.assertEqual(stdout, b'sat\n')
        self.assertFalse(timing['timed_out'])
        self.assertEqual(timing['launch_seconds'], 55)
        self.assertEqual(timing['wait_seconds'], 3)

    def test_creation_overrun_never_grants_another_full_solve_budget(self):
        process = Mock(pid=17, returncode=-9)
        process.wait.side_effect = [subprocess.TimeoutExpired('solver', 0), -9]
        with patch('tools.process_budget.subprocess.Popen', return_value=process), \
                patch('tools.process_budget.time.monotonic', side_effect=[0, 226, 226.01, 226.1]), \
                patch('tools.process_budget.os.killpg') as kill:
            _, _, timing = run_with_budget(['solver'], 60, {})
        self.assertEqual(process.wait.call_args_list[0].kwargs['timeout'], 0)
        kill.assert_called_once()
        self.assertTrue(timing['timed_out'])
        self.assertTrue(timing['budget_overrun'])

    def test_normal_timeout_cleanup_and_already_exited_process(self):
        process = Mock(pid=17, returncode=-9)
        process.wait.side_effect = [subprocess.TimeoutExpired('solver', 59), -9]
        with patch('tools.process_budget.subprocess.Popen', return_value=process), \
                patch('tools.process_budget.time.monotonic', side_effect=[0, 1, 60, 60.1]), \
                patch('tools.process_budget.os.killpg', side_effect=ProcessLookupError):
            _, _, timing = run_with_budget(['solver'], 60, {})
        self.assertTrue(timing['timed_out'])
        self.assertFalse(timing['budget_overrun'])

    def test_slow_reaping_is_distinct_from_late_timeout_notification(self):
        process = Mock(pid=17, returncode=-9)
        process.wait.side_effect = [subprocess.TimeoutExpired('solver', 60), -9]
        with patch('tools.process_budget.subprocess.Popen', return_value=process), \
                patch('tools.process_budget.time.monotonic', side_effect=[0, .001, 60.05, 283]), \
                patch('tools.process_budget.os.killpg'):
            _, _, timing = run_with_budget(['solver'], 60, {})
        self.assertEqual(timing['timeout_notified_seconds'], 60.05)
        self.assertAlmostEqual(timing['cleanup_seconds'], 222.95)
        self.assertTrue(timing['budget_overrun'])

    @unittest.skipUnless(hasattr(os, 'fork'), 'requires POSIX process groups')
    def test_detached_output_holder_does_not_extend_the_solver_lifetime(self):
        with tempfile.TemporaryDirectory() as directory:
            pid_file = Path(directory) / 'child.pid'
            script = ('import os,sys,time; child=os.fork(); '
                      'os.setsid() if child==0 else None; '
                      'time.sleep(3) if child==0 else None; '
                      'os._exit(0) if child==0 else None; '
                      'open(sys.argv[1],"w").write(str(child)); '
                      'print("sat",flush=True); os._exit(0)')
            try:
                stdout, _, timing = run_with_budget([sys.executable, '-c', script, str(pid_file)],
                                                   1, dict(os.environ))
                self.assertEqual(stdout, b'sat\n')
                self.assertEqual(timing['returncode'], 0)
                self.assertFalse(timing['timed_out'])
            finally:
                if pid_file.exists():
                    try:
                        os.kill(int(pid_file.read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass


if __name__ == '__main__':
    unittest.main()
