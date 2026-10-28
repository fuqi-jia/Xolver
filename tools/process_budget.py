"""Measure a subprocess with one wall budget, including process creation."""
import os
import signal
import subprocess
import tempfile
import time


def run_with_budget(command, timeout, environment):
    start = time.monotonic()
    # The process can exit while another process still holds its output
    # descriptors. File-backed capture lets us wait for the actual child.
    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        process = subprocess.Popen(command, stdout=stdout_file, stderr=stderr_file,
                                   start_new_session=True, env=environment)
        launched = time.monotonic()
        expired = False
        notified = None
        try:
            process.wait(timeout=max(0, timeout - (launched - start)))
        except subprocess.TimeoutExpired:
            expired = True
            notified = time.monotonic()
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
        end = time.monotonic()
        stdout_file.seek(0)
        stderr_file.seek(0)
        stdout, stderr = stdout_file.read(), stderr_file.read()
    return stdout, stderr, dict(seconds=end - start, launch_seconds=launched - start,
                               wait_seconds=end - launched, returncode=process.returncode,
                               timeout_notified_seconds=None if notified is None else notified - start,
                               cleanup_seconds=None if notified is None else end - notified,
                               timed_out=expired or end - start > timeout,
                               budget_overrun=end - start > timeout + 1)
