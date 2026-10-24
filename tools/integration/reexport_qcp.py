#!/usr/bin/env python3
"""Export a frozen set of QCP Rocq goals using the current typed adapter."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import export_goals


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--corpus', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    original = args.corpus.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    report = json.loads((original / 'manifest.json').read_text())
    report['original_manifest_sha256'] = hashlib.sha256((original / 'manifest.json').read_bytes()).hexdigest()
    report['exporter_sha256'] = hashlib.sha256(Path(__file__).with_name('qcp.py').read_bytes()).hexdigest()
    report['queries'] = []
    for row in report['programs']:
        folder = original / row['directory']
        if row.get('returncode') != 0 or not (folder / 'goal.v').is_file():
            continue
        exported_before = json.loads((folder / 'queries/manifest.json').read_text())
        digest = hashlib.sha256((folder / 'goal.v').read_bytes()).hexdigest()
        if digest != exported_before['source_sha256']:
            raise ValueError('original Rocq goal hash changed')
        target = args.output / row['directory'] / 'queries'
        exported = export_goals(folder / 'goal.v', target)
        for query in exported['queries']:
            report['queries'].append({**query, 'source': row['source'],
                'file': f'{row["directory"]}/queries/{query["file"]}'})
    (args.output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'programs': len(report['programs']), 'queries': len(report['queries'])}))


if __name__ == '__main__':
    main()
