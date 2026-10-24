#!/usr/bin/env python3
"""Generate QCP goals and export typed pure conditions outside its checkout."""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import export_goals


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--qcp', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--revision', required=True)
    p.add_argument('--count', type=int, default=32)
    p.add_argument('--program', action='append', default=[])
    p.add_argument('--timeout', type=float, default=30)
    args = p.parse_args()
    root, out = args.qcp.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    commands = []
    for line in (root / 'run-example-linux.sh').read_text().splitlines():
        if not line.startswith('linux-binary/symexec '):
            continue
        command = shlex.split(line.rstrip(';'))
        source = next((a.split('=', 1)[1] for a in command if a.startswith('--input-file=')), None)
        if source:
            commands.append((source, command))
    if args.program:
        requested = set(args.program)
        commands = [x for x in commands if x[0] in requested]
        if {s for s, _ in commands} != requested:
            raise ValueError('a requested program is absent from the pinned QCP runner')
    else:
        # Round-robin across example directories; keep source identities intact.
        groups = {}
        for source, command in commands:
            groups.setdefault(str(Path(source).parent), []).append((source, command))
        commands = []
        while groups and len(commands) < args.count:
            for group in list(groups):
                commands.append(groups[group].pop(0))
                if not groups[group]:
                    del groups[group]
                if len(commands) == args.count:
                    break
    report = {'qcp_revision': args.revision, 'qcp_binary_sha256': digest(root / 'linux-binary/symexec'),
              'programs': [], 'queries': [], 'program_verified': False}
    for index, (source, original) in enumerate(commands):
        folder = out / f'program-{index:03d}'
        folder.mkdir()
        command = [str(root / 'linux-binary/symexec')] + [a for a in original[1:] if not a.startswith(
            ('--goal-file=', '--proof-auto-file=', '--proof-manual-file='))]
        command += ['--goal-file=' + str(folder / 'goal.v'),
                    '--proof-auto-file=' + str(folder / 'auto.v'),
                    '--proof-manual-file=' + str(folder / 'manual.v'), '--no-strategy-gen']
        row = {'source': source, 'source_sha256': digest(root / source), 'command': command,
               'cwd': str(root), 'directory': folder.name}
        start = time.monotonic()
        try:
            ran = subprocess.run(command, cwd=root, text=True, capture_output=True, timeout=args.timeout)
            row['returncode'] = ran.returncode
            (folder / 'stdout.txt').write_text(ran.stdout)
            (folder / 'stderr.txt').write_text(ran.stderr)
            if ran.returncode == 0 and (folder / 'goal.v').is_file():
                exported = export_goals(folder / 'goal.v', folder / 'queries')
                row['goals'] = len(exported['goals'])
                row['exported'] = len(exported['queries'])
                row['unsupported'] = sum(g['status'] == 'unsupported' for g in exported['goals'])
                for query in exported['queries']:
                    report['queries'].append({**query, 'source': source,
                        'file': f'{folder.name}/queries/{query["file"]}'})
        except subprocess.TimeoutExpired:
            row['returncode'] = 'timeout'
        row['seconds'] = time.monotonic() - start
        report['programs'].append(row)
        (folder / 'run.json').write_text(json.dumps(row, indent=2) + '\n')
        (out / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
        print(source, row['returncode'], row.get('exported', 0), flush=True)
    print(json.dumps({'programs': len(report['programs']), 'queries': len(report['queries'])}))


if __name__ == '__main__':
    main()
