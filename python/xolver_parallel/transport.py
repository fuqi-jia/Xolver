"""Bounded, deadline-driven pipes for reusable POSIX worker processes."""
import math
import os
import selectors
import signal
import struct
import subprocess
import tempfile
import time

HEADER = struct.Struct('!Q')
MAX_BYTES = 64 * 1024 * 1024


def frame(message, maximum=MAX_BYTES):
    if not 0 < len(message) <= maximum:
        raise ValueError('empty or oversized worker frame')
    return HEADER.pack(len(message)) + message


class ProcessChannel:
    """One owned process; callers serialize requests and supply absolute deadlines.

    The process starts lazily, so startup consumes the first request's budget.
    A failed exchange must close the channel; unread replies cannot be reused.
    Diagnostics use a file to avoid blocking the child on an unconsumed pipe.
    """
    def __init__(self, argv, *, environment=None, max_bytes=MAX_BYTES):
        if isinstance(argv, (str, bytes)) or not argv or any(not isinstance(v, str) for v in argv):
            raise TypeError('worker argv must be a nonempty sequence of strings')
        if type(max_bytes) is not int or max_bytes <= 0:
            raise ValueError('message budget must be a positive integer')
        self.argv = tuple(argv)
        self.environment = environment
        self.max_bytes = max_bytes
        self.process = None
        self._stderr = None
        self._buffer = bytearray()
        self._closed = False

    @staticmethod
    def remaining(deadline):
        remaining = deadline - time.monotonic()
        if not math.isfinite(remaining) or remaining <= 0:
            raise TimeoutError('worker request exceeded its wall budget')
        return remaining

    def start(self, deadline):
        self.remaining(deadline)
        if self._closed:
            raise RuntimeError('worker channel is closed')
        if self.process is None:
            self._stderr = tempfile.TemporaryFile()
            try:
                self.process = subprocess.Popen(self.argv, stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, stderr=self._stderr, bufsize=0,
                    start_new_session=True, env=self.environment)
                os.set_blocking(self.process.stdin.fileno(), False)
                os.set_blocking(self.process.stdout.fileno(), False)
            except BaseException:
                self.close()
                raise
        self.remaining(deadline)
        if self.process.poll() is not None:
            raise RuntimeError('worker exited with status {}'.format(self.process.returncode))

    def _ready(self, pipe, event, deadline):
        with selectors.DefaultSelector() as selector:
            selector.register(pipe, event)
            if not selector.select(self.remaining(deadline)):
                raise TimeoutError('worker pipe exceeded its wall budget')
        self.remaining(deadline)

    def write(self, data, deadline):
        self.start(deadline)
        offset = 0
        while offset < len(data):
            self._ready(self.process.stdin, selectors.EVENT_WRITE, deadline)
            try:
                offset += os.write(self.process.stdin.fileno(), memoryview(data)[offset:offset + 65536])
            except BlockingIOError:
                continue

    def _fill(self, deadline):
        self._ready(self.process.stdout, selectors.EVENT_READ, deadline)
        try:
            data = os.read(self.process.stdout.fileno(), min(65536, self.max_bytes + 1 - len(self._buffer)))
        except BlockingIOError:
            return
        if not data:
            raise RuntimeError('worker closed stdout before its reply was complete')
        self._buffer.extend(data)
        if len(self._buffer) > self.max_bytes:
            raise ValueError('worker response exceeds message budget')

    def read_exact(self, length, deadline):
        if not 0 < length <= self.max_bytes:
            raise ValueError('empty or oversized worker response')
        while len(self._buffer) < length:
            self._fill(deadline)
        self.remaining(deadline)
        result = bytes(self._buffer[:length])
        del self._buffer[:length]
        return result

    def read_line(self, deadline):
        while b'\n' not in self._buffer:
            self._fill(deadline)
        length = self._buffer.index(b'\n') + 1
        return self.read_exact(length, deadline)

    def diagnostics(self, offset=0):
        if self._stderr is None:
            return b'', 0
        end = os.fstat(self._stderr.fileno()).st_size
        if end - offset > self.max_bytes:
            raise ValueError('worker diagnostics exceed message budget')
        # pread does not disturb the child's inherited file position.
        return os.pread(self._stderr.fileno(), end - offset, offset), end

    def close(self):
        if self._closed:
            return
        self._closed = True
        if self.process is not None:
            # Reap the process and kill its group even if its leader has exited:
            # a descendant must not survive a failed or cancelled request.
            try:
                os.killpg(self.process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.process.wait()
            self.process.stdin.close()
            self.process.stdout.close()
        if self._stderr is not None:
            self._stderr.close()

    def finish(self):
        """Close input and require a clean exit; abort only on failure/timeout."""
        if self._closed:
            return
        try:
            if self.process is not None:
                self.process.stdin.close()
                try:
                    code = self.process.wait(timeout=1)
                except subprocess.TimeoutExpired as error:
                    raise TimeoutError('worker did not finish after input EOF') from error
                if code:
                    raise RuntimeError('worker failed at shutdown with status {}'.format(code))
                if self._buffer:
                    raise ValueError('worker sent unsolicited reply bytes')
                try:
                    trailing = os.read(self.process.stdout.fileno(), 1)
                except BlockingIOError as error:
                    raise RuntimeError('worker left stdout open after exit') from error
                if trailing:
                    raise ValueError('worker sent unsolicited reply bytes')
        finally:
            self.close()

    def __enter__(self):
        return self

    def __exit__(self, error_type, *_):
        self.close() if error_type else self.finish()
