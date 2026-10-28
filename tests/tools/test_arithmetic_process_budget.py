import subprocess
import sys
from pathlib import Path
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/remote'))
from compare_arithmetic_case import run_with_budget


class ArithmeticProcessBudget(unittest.TestCase):
    def test_slow_process_creation_consumes_the_existing_budget(self):
        process = Mock(pid=17, returncode=0)
        process.communicate.return_value = (b'sat\n', b'')
        with patch('compare_arithmetic_case.subprocess.Popen', return_value=process), \
                patch('compare_arithmetic_case.time.monotonic', side_effect=[0, 55, 58]):
            stdout, _, timing = run_with_budget(['solver'], 60, {})
        process.communicate.assert_called_once_with(timeout=5)
        self.assertEqual(stdout, b'sat\n')
        self.assertFalse(timing['timed_out'])
        self.assertEqual(timing['launch_seconds'], 55)
        self.assertEqual(timing['wait_seconds'], 3)

    def test_creation_overrun_never_grants_another_full_solve_budget(self):
        process = Mock(pid=17, returncode=-9)
        process.communicate.side_effect = [subprocess.TimeoutExpired('solver', 0), (b'', b'')]
        with patch('compare_arithmetic_case.subprocess.Popen', return_value=process), \
                patch('compare_arithmetic_case.time.monotonic', side_effect=[0, 226, 226.1]), \
                patch('compare_arithmetic_case.os.killpg') as kill:
            _, _, timing = run_with_budget(['solver'], 60, {})
        self.assertEqual(process.communicate.call_args_list[0].kwargs['timeout'], 0)
        kill.assert_called_once()
        self.assertTrue(timing['timed_out'])
        self.assertTrue(timing['budget_overrun'])

    def test_normal_timeout_cleanup_and_already_exited_process(self):
        process = Mock(pid=17, returncode=-9)
        process.communicate.side_effect = [subprocess.TimeoutExpired('solver', 59), (b'', b'')]
        with patch('compare_arithmetic_case.subprocess.Popen', return_value=process), \
                patch('compare_arithmetic_case.time.monotonic', side_effect=[0, 1, 60.1]), \
                patch('compare_arithmetic_case.os.killpg', side_effect=ProcessLookupError):
            _, _, timing = run_with_budget(['solver'], 60, {})
        self.assertTrue(timing['timed_out'])
        self.assertFalse(timing['budget_overrun'])


if __name__ == '__main__':
    unittest.main()
