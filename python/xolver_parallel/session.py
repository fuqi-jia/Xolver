"""Reusable named-task sessions with fresh solver state for every task."""
import threading
import time

from .protocol import decode_results, encode_tasks
from .transport import HEADER, ProcessChannel, frame


class WorkerSession:
    def __init__(self, worker, *, environment=None):
        self.worker = worker
        self.channel = ProcessChannel(worker.argv, environment=environment,
                                      max_bytes=worker.max_bytes)
        self._lock = threading.Lock()

    def run(self, tasks, *, deadline=None):
        # Encoding, lock contention and initial process creation share the same
        # wall budget. An expired request never leaks a later reply to a caller.
        deadline = min(deadline, time.monotonic() + self.worker.timeout) if deadline is not None \
            else time.monotonic() + self.worker.timeout
        if not self._lock.acquire(timeout=self.channel.remaining(deadline)):
            raise TimeoutError('worker session lock exceeded its wall budget')
        try:
            request = frame(encode_tasks(tasks), self.worker.max_bytes)
            self.channel.write(request, deadline)
            length, = HEADER.unpack(self.channel.read_exact(HEADER.size, deadline))
            response = self.channel.read_exact(length, deadline)
            results = decode_results(response, tasks)
            self.channel.remaining(deadline)
            return results
        except BaseException:
            self.channel.close()
            raise
        finally:
            self._lock.release()

    def close(self):
        with self._lock:
            self.channel.finish()

    def __enter__(self):
        return self

    def __exit__(self, error_type, *_):
        if error_type:
            self.channel.close()
        else:
            self.close()
