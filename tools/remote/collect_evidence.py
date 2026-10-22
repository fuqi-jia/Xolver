#!/usr/bin/env python3
"""Archive validation records without copying binaries or an incremental build."""
import argparse
import hashlib
import json
from pathlib import Path
import sqlite3
import tarfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--eos-db', type=Path)
    parser.add_argument('--output', type=Path, default=ROOT / 'validation/evidence.tar.gz')
    parser.add_argument('--include', action='append', default=[],
                        help='Validation-relative file or directory (repeatable; default all)')
    parser.add_argument('--experiment', action='append', default=[],
                        help='Exact EOS experiment name (repeatable; default all Xolver audits)')
    args = parser.parse_args()
    validation = ROOT / 'validation'
    validation.mkdir(exist_ok=True)
    if args.eos_db:
        # Evidence collection never updates ExperimentOS state.
        with sqlite3.connect(args.eos_db.resolve().as_uri() + '?mode=ro', uri=True) as db:
            db.row_factory = sqlite3.Row
            rows = [dict(row) for row in db.execute(
                'SELECT e.name AS experiment_name, r.* FROM run r '
                'JOIN experiment e ON e.id=r.experiment_id WHERE e.name LIKE ?',
                ('xolver-%',))]
        if args.experiment:
            rows = [row for row in rows if row['experiment_name'] in args.experiment]
        index_name = args.output.stem + '-eos-runs.json' if args.include else 'eos-runs.json'
        (validation / index_name).write_text(json.dumps(rows, indent=2) + '\n')
        if args.include:
            args.include.append(index_name)
        for row in rows:
            workdir = Path(row['workdir']) if row['workdir'] else None
            if not workdir:
                continue
            dest = validation / 'eos' / row['id']
            if args.include:
                args.include.append('eos/' + row['id'])
            for name in ['run.log', 'metrics.json']:
                source = workdir / name
                if source.is_file():
                    dest.mkdir(parents=True, exist_ok=True)
                    (dest / name).write_bytes(source.read_bytes())

    allowed = {'.json', '.log', '.xml', '.txt', '.rc', '.sha256', '.stdout',
               '.stderr', '.smt2', '.cnf', '.drat', '.drat-output', '.alethe',
               '.carcara-output', '.queries', '.thy', '.ML', '.v', '.py', '.sh', '.md', '.yaml'}
    records = []
    manifest_path = args.output.with_suffix('.manifest.json')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(args.output, 'w:gz') as archive:
        for path in sorted(validation.rglob('*')):
            if not path.is_file() or path.is_symlink():
                continue
            if path.resolve() in {args.output.resolve(), manifest_path.resolve()}:
                continue
            if path.suffix not in allowed and path.name not in {
                    'started', 'finished', 'host', 'ROOT', 'ROOT.batch'}:
                continue
            relative = path.relative_to(validation).as_posix()
            if args.include and not any(relative == prefix or relative.startswith(prefix.rstrip('/') + '/')
                                        for prefix in args.include):
                continue
            # .txt permits versioning logs despite the repository's *.log ignore.
            archived = relative + '.txt' if path.suffix == '.log' else relative
            archive.add(path, arcname=archived)
            records.append({'source': relative, 'archive_path': archived,
                            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                            'bytes': path.stat().st_size})
    manifest = {'archive': args.output.name,
                'sha256': hashlib.sha256(args.output.read_bytes()).hexdigest(),
                'records': records}
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'{len(records)} records -> {args.output}')


if __name__ == '__main__':
    main()
