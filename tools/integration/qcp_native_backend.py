#!/usr/bin/env python3
"""Select the actual native QCP SAT backend; this does not certify a C program."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import socket
import struct
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'python'))
from tools.integration.qcp import Unsupported
from tools.integration.qcp_backend import leased_cpu
from tools.integration.qcp_native import formula_query
from xolver_parallel import Task
from xolver_parallel.protocol import decode_results, encode_tasks
from xolver_parallel.transport import HEADER, ProcessChannel, frame

QCP_SHA256 = '0e74c446cebca8c804ff9b838f07c67f23e31a093630675bc720b25c986e1032'
QUERY_BYTES = 16 * 1024**2
MEMORY_BYTES = 16 * 1024**3
WALL_NS = 60_000_000_000
FRAME = struct.Struct('!IIQQQ')  # byte count, native mode, ordinal, caller, started-ns


def sha256(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write_json(path: Path, value: dict) -> None:
    # A native parent can exit immediately after a reply. Leave the preceding
    # complete record readable even if its death guard interrupts an update.
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def solver_environment() -> dict:
    controls = json.loads((ROOT / 'src/base/controls.json').read_text())['controls']
    excluded = {entry['name'] for entry in controls} | {'LD_PRELOAD'}
    return {key: value for key, value in os.environ.items()
            if key not in excluded and not key.startswith('XOLVER_QCP_')}


class BackendSession:
    """One selected backend process, with a fresh context for each occurrence."""
    def __init__(self, backend: str, solver: Path, guard: Path):
        if backend not in ('xolver', 'z3'):
            raise ValueError('unsupported backend')
        self.backend = backend
        command = [str(guard), 'prlimit', '--as=' + str(MEMORY_BYTES), '--', str(solver)]
        if backend == 'z3':
            command.append('-in')
        # A cumulative CPU limit would expire a healthy long-lived process.
        # Every query instead has one wall deadline on its leased physical CPU.
        self.channel = ProcessChannel(command, environment=solver_environment())
        self.ordinal = 0
        self.stderr_offset = 0

    def solve(self, script: str, output: Path, started_ns: int) -> dict:
        deadline = (started_ns + WALL_NS) / 1e9
        began = time.monotonic()
        self.channel.remaining(deadline)
        first = self.channel.process is None
        if self.backend == 'xolver':
            payload = json.dumps(dict(smt2=script, model=False,
                timeout_ms=max(1, int(self.channel.remaining(deadline) * 1000)))).encode()
            tasks = [Task(str(self.ordinal), 'smt.solve', payload)]
            request = frame(encode_tasks(tasks), self.channel.max_bytes)
        else:
            # formula_query emits a standalone check-sat/exit script. Remove
            # only its generated final exit for the persistent transport.
            # reset removes declarations, assertions and options from the last
            # occurrence; every occurrence is still solved, including repeats.
            if not script.endswith('(exit)\n'):
                raise ValueError('expected the generated terminal exit command')
            marker = 'qcp-query-{}-done'.format(self.ordinal)
            request = ('(reset)\n(set-option :print-success false)\n'
                '(set-option :timeout {})\n'.format(max(1, int(self.channel.remaining(deadline) * 1000)))
                + script[:-len('(exit)\n')] + '(echo "' + marker + '")\n').encode()
        (output / 'request.bin').write_bytes(request)
        self.channel.write(request, deadline)
        if self.backend == 'xolver':
            header = self.channel.read_exact(HEADER.size, deadline)
            length, = HEADER.unpack(header)
            response = self.channel.read_exact(length, deadline)
            (output / 'response.bin').write_bytes(header + response)
            value = json.loads(decode_results(response, tasks)[0].get())
            result = value.get('result')
            if result not in ('sat', 'unsat', 'unknown'):
                raise ValueError('invalid typed solver result')
        else:
            answer = self.channel.read_line(deadline)
            terminator = self.channel.read_line(deadline)
            (output / 'response.bin').write_bytes(answer + terminator)
            if terminator.strip() != marker.encode():
                raise ValueError('mismatched SMT-LIB response boundary')
            result = answer.strip().decode()
            if result not in ('sat', 'unsat', 'unknown'):
                raise ValueError('invalid SMT-LIB solver result')
        self.channel.remaining(deadline)
        stderr, self.stderr_offset = self.channel.diagnostics(self.stderr_offset)
        (output / 'stdout').write_text(result + '\n')
        (output / 'stderr').write_bytes(stderr)
        record = dict(result=result, command=list(self.channel.argv),
            process_pid=self.channel.process.pid, process_started=first,
            process_query_ordinal=self.ordinal, transport=('task-frame/1'
                if self.backend == 'xolver' else 'smtlib-reset/1'),
            seconds=time.monotonic() - began, returncode=None, timed_out=False,
            stdout_format='normalized-solver-decision',
            request_sha256=sha256(output / 'request.bin'),
            response_sha256=sha256(output / 'response.bin'),
            stdout_sha256=sha256(output / 'stdout'), stderr_sha256=sha256(output / 'stderr'))
        self.ordinal += 1
        return record

    def close(self):
        self.channel.close()

    def abort(self, output: Path) -> dict:
        evidence = dict(command=list(self.channel.argv), process_query_ordinal=self.ordinal)
        if self.channel.process is not None:
            evidence['process_pid'] = self.channel.process.pid
        try:
            stderr, self.stderr_offset = self.channel.diagnostics(self.stderr_offset)
            (output / 'stderr').write_bytes(stderr)
        except Exception as error:
            evidence['diagnostic_error'] = repr(error)
        finally:
            self.close()
        for name in ('request.bin', 'response.bin', 'stderr'):
            if (output / name).exists():
                evidence[name.replace('.bin', '') + '_sha256'] = sha256(output / name)
        return evidence


def decide(formula: str, session: BackendSession, output: Path, started_ns: int) -> dict:
    """One unchanged formula, one selected solver, one shared callback budget."""
    output.mkdir(exist_ok=False)
    (output / 'formula.txt').write_text(formula)
    record = dict(backend=session.backend, formula_sha256=sha256(output / 'formula.txt'),
                  result='error', program_verified=False)
    try:
        script, signature = formula_query(formula)
        query = output / 'query.smt2'
        query.write_text(script)
        record.update(signature=signature, query_sha256=sha256(query))
        if started_ns + WALL_NS <= time.monotonic_ns():
            record['result'] = 'timeout'
        else:
            record.update(session.solve(script, output, started_ns))
    except Unsupported as error:
        record.update(result='unsupported', reason=str(error))
    except TimeoutError as error:
        record.update(session.abort(output))
        record.update(result='timeout', timed_out=True, reason=str(error))
    except Exception as error:
        record.update(session.abort(output))
        record.update(result='error', reason=repr(error))
    record['callback_seconds'] = (time.monotonic_ns() - started_ns) / 1e9
    if record['callback_seconds'] >= 60 and record['result'] in ('sat', 'unsat'):
        session.close()
        record.update(result='timeout', reason='serialization/startup exceeded the shared wall budget')
    write_json(output / 'record.json', record)
    return record


def receive(connection: socket.socket, length: int, allow_eof: bool = False) -> bytes:
    data = bytearray()
    while len(data) < length:
        chunk = connection.recv(length - len(data))
        if not chunk:
            if allow_eof and not data:
                return b''
            raise ValueError('truncated native SAT protocol frame')
        data.extend(chunk)
    return bytes(data)


def run_worker(descriptor: int, backend: str, solver: Path, guard: Path, output: Path) -> int:
    cpu = leased_cpu()
    solver_hash, guard_hash = sha256(solver), sha256(guard)
    report = dict(schema=2, integration='native-qcp-sat-entry', backend=backend,
                  solver=dict(path=str(solver), sha256=solver_hash),
                  guard_sha256=guard_hash, worker_sha256=sha256(Path(__file__)),
                  parser_sha256=sha256(ROOT / 'tools/integration/qcp_native.py'),
                  transport_sha256=sha256(ROOT / 'python/xolver_parallel/transport.py'),
                  cpu=cpu, wall_seconds=60, memory_bytes=MEMORY_BYTES, calls=[],
                  complete=False, program_verified=False, errors=[])
    write_json(output / 'session.json', report)
    session = BackendSession(backend, solver, guard)
    try:
        with socket.socket(fileno=descriptor) as connection:
            while True:
                header = receive(connection, FRAME.size, allow_eof=True)
                if not header:
                    report['complete'] = True
                    break
                length, mode, ordinal, caller, started_ns = FRAME.unpack(header)
                if not 0 < length <= QUERY_BYTES or mode not in (0, 1) or ordinal != len(report['calls']):
                    raise ValueError('invalid native SAT protocol header')
                formula = receive(connection, length).decode('utf-8')
                query = output / f'query-{ordinal:05d}'
                row = decide(formula, session, query, started_ns)
                report['calls'].append(dict(ordinal=ordinal, mode=mode, caller=hex(caller),
                    result=row['result'], query=str(query),
                    formula_sha256=row['formula_sha256'],
                    query_sha256=row.get('query_sha256'), callback_seconds=row['callback_seconds']))
                # A non-definite result has no sound representation in the
                # pinned native ABI. Retain its evidence and stop the host.
                reply = {'unsat': b'0', 'sat': b'1'}.get(row['result'], b'E')
                if reply == b'E':
                    report['errors'].append('selected solver returned ' + row['result'])
                # Persist the failure before replying: the native parent may
                # immediately exit and its death guard can kill this worker.
                write_json(output / 'session.json', report)
                connection.sendall(reply)
                if reply == b'E':
                    break
        if sha256(solver) != solver_hash or sha256(guard) != guard_hash:
            raise ValueError('frozen backend executable changed')
    except Exception as error:
        report['complete'] = False
        report['errors'].append(repr(error))
    finally:
        report['solver_processes'] = int(session.channel.process is not None)
        report['solver_queries'] = session.ordinal
        try:
            if report['complete'] and not report['errors']:
                session.channel.finish()
            else:
                session.close()
        except Exception as error:
            report['complete'] = False
            report['errors'].append(repr(error))
    write_json(output / 'session.json', report)
    return int(not report['complete'] or bool(report['errors']))


def launch(binary: Path, library: Path, backend: str, solver: Path,
           guard: Path, output: Path, command: list[str]) -> int:
    cpu = leased_cpu()
    if sha256(binary) != QCP_SHA256:
        raise ValueError('native adapter requires the qualified QCP binary SHA-256')
    if not command:
        raise ValueError('supply the native QCP or controller command after --')
    output.mkdir(parents=True, exist_ok=False)
    files = dict(qcp=binary, library=library, solver=solver, guard=guard,
                 worker=Path(__file__).resolve(), parser=ROOT / 'tools/integration/qcp_native.py',
                 transport=ROOT / 'python/xolver_parallel/transport.py',
                 protocol=ROOT / 'python/xolver_parallel/protocol.py')
    identities = {name: dict(path=str(path), sha256=sha256(path)) for name, path in files.items()}
    report = dict(schema=1, command=command, files=identities, backend=backend,
                  cpu=cpu, wall_seconds_per_query=60, memory_bytes=MEMORY_BYTES,
                  program_verified=False, complete=False, sessions=[], errors=[])
    write_json(output / 'launch.json', report)
    environment = dict(os.environ, XOLVER_QCP_BINARY=str(binary),
        XOLVER_QCP_PYTHON=sys.executable, XOLVER_QCP_WORKER=str(Path(__file__).resolve()),
        XOLVER_QCP_BACKEND=backend, XOLVER_QCP_SOLVER=str(solver),
        XOLVER_QCP_EXEC_GUARD=str(guard), XOLVER_QCP_OUTPUT=str(output))
    environment['LD_PRELOAD'] = str(library) + (' ' + environment['LD_PRELOAD']
                                               if environment.get('LD_PRELOAD') else '')
    started = time.monotonic()
    try:
        # The guard also ties the controller/native process to this launcher.
        result = subprocess.run([str(guard), *command], env=environment)
        report['returncode'] = result.returncode
        for folder in sorted(output.glob('session-*')):
            path = folder / 'session.json'
            session = json.loads(path.read_text()) if path.exists() else dict(complete=False, calls=[])
            report['sessions'].append(dict(path=str(folder), complete=session['complete'],
                calls=len(session['calls']), errors=session.get('errors', [])))
        for name, path in files.items():
            if sha256(path) != identities[name]['sha256']:
                report['errors'].append('frozen file changed: ' + name)
        report['complete'] = result.returncode == 0 and not report['errors'] and all(
            session['complete'] and not session['errors'] for session in report['sessions'])
    except Exception as error:
        report['errors'].append(repr(error))
    report['seconds'] = time.monotonic() - started
    write_json(output / 'launch.json', report)
    return 0 if report['complete'] else 125


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend', choices=['xolver', 'z3'], required=True)
    parser.add_argument('--solver', type=Path, required=True,
                        help='frozen xolver-parallel-worker or Z3 executable')
    parser.add_argument('--exec-guard', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--qcp-binary', type=Path)
    parser.add_argument('--library', type=Path)
    parser.add_argument('--worker-fd', type=int, help=argparse.SUPPRESS)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        solver, guard = (path.resolve(strict=True) for path in (args.solver, args.exec_guard))
        output = args.output.resolve()
        if args.worker_fd is not None:
            return run_worker(args.worker_fd, args.backend, solver, guard, output)
        if args.qcp_binary is None or args.library is None:
            parser.error('--qcp-binary and --library are required for launching')
        command = args.command[1:] if args.command[:1] == ['--'] else args.command
        return launch(args.qcp_binary.resolve(strict=True), args.library.resolve(strict=True),
                      args.backend, solver, guard, output, command)
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 125


if __name__ == '__main__':
    raise SystemExit(main())
