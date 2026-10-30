"""Transport lifetime checks with deliberately fragmented and faulty children."""
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'python'))
from xolver_parallel import Task, Worker, WorkerSession
from xolver_parallel.transport import ProcessChannel


class WorkerTransportTests(unittest.TestCase):
    def test_fragmented_frames_and_repeated_requests_share_one_process(self):
        child = '''import json, os, struct, sys
while True:
    header = sys.stdin.buffer.read(8)
    if not header: break
    message = json.loads(sys.stdin.buffer.read(struct.unpack('!Q', header)[0]))
    results = [dict(id=t['id'], ok=True, payload=t['payload'], error='') for t in message['tasks']]
    body = json.dumps(dict(version=1, results=results)).encode()
    wire = struct.pack('!Q', len(body)) + body
    for byte in wire:
        os.write(1, bytes([byte]))
'''
        with WorkerSession(Worker((sys.executable, '-u', '-c', child))) as session:
            pid = None
            for index in range(3):
                payload = bytes([0, 255, index])
                self.assertEqual(session.run([Task(str(index), 'echo', payload)])[0].get(), payload)
                if pid is not None:
                    self.assertEqual(session.channel.process.pid, pid)
                pid = session.channel.process.pid
        self.assertIsNotNone(session.channel.process.returncode)
        self.assertEqual(session.channel.process.returncode, 0)

    def test_a_failure_after_the_last_reply_is_not_hidden_by_shutdown(self):
        script = '''import json, os, struct, sys
size = struct.unpack('!Q', sys.stdin.buffer.read(8))[0]
task = json.loads(sys.stdin.buffer.read(size))['tasks'][0]
body = json.dumps(dict(version=1, results=[dict(id=task['id'], ok=True, payload=[], error='')])).encode()
os.write(1, struct.pack('!Q', len(body)) + body)
sys.stdin.buffer.read(1)
sys.exit(7)
'''
        session = WorkerSession(Worker((sys.executable, '-c', script)))
        with self.assertRaisesRegex(RuntimeError, 'shutdown'):
            with session:
                self.assertEqual(session.run([Task('last', 'echo')])[0].get(), b'')
        self.assertEqual(session.channel.process.returncode, 7)

    def test_bad_length_and_truncated_payload_close_the_process(self):
        for output in (struct.pack('!Q', 0), struct.pack('!Q', 1025),
                       struct.pack('!Q', 10) + b'abc'):
            script = 'import os; os.read(0, 4096); os.write(1, ' + repr(output) + ')'
            session = WorkerSession(Worker((sys.executable, '-c', script), max_bytes=1024))
            with self.subTest(output=output), self.assertRaises((ValueError, RuntimeError)):
                session.run([Task('x', 'echo')])
            self.assertIsNotNone(session.channel.process.returncode)

    def test_unsolicited_bytes_after_the_last_reply_are_rejected(self):
        script = '''import json, os, struct, sys
size = struct.unpack('!Q', sys.stdin.buffer.read(8))[0]
task = json.loads(sys.stdin.buffer.read(size))['tasks'][0]
body = json.dumps(dict(version=1, results=[dict(id=task['id'], ok=True, payload=[], error='')])).encode()
os.write(1, struct.pack('!Q', len(body)) + body)
sys.stdin.buffer.read(1)
os.write(1, b'unrequested response')
'''
        with self.assertRaisesRegex(ValueError, 'unsolicited'):
            with WorkerSession(Worker((sys.executable, '-c', script))) as session:
                self.assertEqual(session.run([Task('last', 'echo')])[0].get(), b'')

    def test_cancelled_read_kills_descendants_and_cannot_reuse_a_reply(self):
        with tempfile.TemporaryDirectory() as name:
            pid_file = Path(name) / 'child.pid'
            script = '''import os, subprocess, sys, time
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(300)'])
open(sys.argv[1], 'w').write(str(child.pid))
os.read(0, 4096)
time.sleep(300)
'''
            session = WorkerSession(Worker((sys.executable, '-c', script, str(pid_file)), timeout=1))
            started = time.monotonic()
            with self.assertRaises(TimeoutError):
                session.run([Task('hung', 'echo')])
            self.assertLess(time.monotonic() - started, 3)
            self.assertIsNotNone(session.channel.process.returncode)
            with self.assertRaises(RuntimeError):
                session.run([Task('next', 'echo')])
            pid = int(pid_file.read_text())
            # A killed orphan can briefly remain a zombie until init reaps it.
            state = Path('/proc') / str(pid) / 'stat'
            for _ in range(100):
                if not state.exists() or state.read_text().rsplit(')', 1)[1].split()[0] in ('Z', 'X'):
                    break
                time.sleep(0.01)
            if state.exists():
                self.assertIn(state.read_text().rsplit(')', 1)[1].split()[0], ('Z', 'X'))

    def test_deadline_already_expired_never_starts_a_process(self):
        with ProcessChannel(('unused',)) as channel:
            with self.assertRaises(TimeoutError):
                channel.write(b'x', time.monotonic() - 1)
            self.assertIsNone(channel.process)

    def test_nonfinite_budgets_are_rejected(self):
        for value in (float('nan'), float('inf'), 0, -1):
            with self.assertRaises(ValueError):
                Worker(('unused',), timeout=value)


if __name__ == '__main__':
    unittest.main()
