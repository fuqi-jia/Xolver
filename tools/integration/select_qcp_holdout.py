#!/usr/bin/env python3
"""Freeze unseen QCP program families without inspecting solver outcomes."""
import argparse
import hashlib
import json
from pathlib import Path
import shlex


def choose(root, development, count=64, seed='20261025'):
    known = development['programs']
    families = {str(Path(p['source']).parent) for p in known}
    names = {Path(p['source']).stem for p in known}
    hashes = {p['source_sha256'] for p in known}
    # CI fixtures also belong to development, even if not in the 32-program run.
    names.update({'gcd', 'Always_pos'})
    groups = {}
    excluded = []
    for line in (root / 'run-example-linux.sh').read_text().splitlines():
        if not line.startswith('linux-binary/symexec '):
            continue
        argv = shlex.split(line.rstrip(';'))
        source = next(a.split('=', 1)[1] for a in argv if a.startswith('--input-file='))
        path = root / source
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        family = str(Path(source).parent)
        row = dict(source=source, source_sha256=digest, family=family)
        if family in families or path.stem in names or digest in hashes:
            excluded.append(row)
            continue
        groups.setdefault(family, []).append(row)
    rank = lambda value: hashlib.sha256((str(seed) + ':' + value).encode()).hexdigest()
    selected = []
    used_hashes = set()
    for family in sorted(groups, key=rank):
        candidates = sorted(groups[family], key=lambda r: rank(r['source']))
        for row in candidates:
            if row['source_sha256'] in used_hashes:
                continue
            selected.append(row)
            used_hashes.add(row['source_sha256'])
            break
        if len(selected) == count:
            break
    if len(selected) < count:
        raise ValueError(f'only {len(selected)} independent eligible families')
    return dict(seed=seed, selected=selected, excluded_development=excluded,
                eligible_families=len(groups), policy='one program per unseen family; no basename or source-hash overlap; no solver outcomes used')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--qcp', type=Path, required=True)
    p.add_argument('--development', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--count', type=int, default=64)
    args = p.parse_args()
    development = json.loads(args.development.read_text())
    report = choose(args.qcp, development, args.count)
    report['development_manifest_sha256'] = hashlib.sha256(args.development.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(len(report['selected']), 'unseen source families frozen')


if __name__ == '__main__':
    main()
