#!/usr/bin/env python3
"""Check licensed, pinned QCP pure-condition excerpts through SV and Z3."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import export_goals


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--sv', type=Path, required=True)
    p.add_argument('--z3', type=Path, required=True)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parents[2]
    fixture = root / 'tests/integration/qcp/integer_goals.v'
    provenance = json.loads((fixture.parent / 'provenance.json').read_text())
    text = fixture.read_text()
    for excerpt in provenance['excerpts']:
        import re
        match = re.search(r'\bDefinition ' + re.escape(excerpt['name']) + r'\s*:=.*?\n\.', text, re.S)
        if not match or hashlib.sha256(match[0].encode()).hexdigest() != excerpt['excerpt_sha256']:
            raise ValueError('QCP fixture provenance mismatch')
    exported = export_goals(fixture, args.output / 'program/queries')
    if len(exported['goals']) != len(provenance['excerpts']) or any(g['status'] != 'exported' for g in exported['goals']):
        raise ValueError('QCP fixture lost coverage')
    for query in exported['queries']:
        query['file'] = 'program/queries/' + query['file']
    (args.output / 'manifest.json').write_text(json.dumps(exported, indent=2) + '\n')
    subprocess.run([sys.executable, str(Path(__file__).with_name('compare_qcp.py')),
                    '--corpus', str(args.output), '--output', str(args.output / 'comparison'),
                    '--solver', str(args.solver), '--sv', str(args.sv), '--z3', str(args.z3)], check=True)
    report = json.loads((args.output / 'comparison/report.json').read_text())
    if report['shared_decisions'] != len(exported['queries']):
        raise RuntimeError('standard SMT, SV and Z3 must all decide the fixture conditions')
    print(json.dumps({'queries': len(exported['queries']), 'interval_certificates': report['interval_certificates'], 'failures': 0}))


if __name__ == '__main__':
    main()
