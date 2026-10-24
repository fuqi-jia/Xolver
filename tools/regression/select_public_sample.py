#!/usr/bin/env python3
"""Freeze a family-stratified arithmetic sample before measuring any solver."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re


def select(root, sizes, seed='20261025'):
    rank = lambda value: hashlib.sha256((seed + ':' + value).encode()).hexdigest()
    result = []
    populations = {}
    for logic, count in sizes.items():
        groups = collections.defaultdict(list)
        for path in (root / logic).rglob('*.smt2'):
            relative = path.relative_to(root)
            family = relative.parts[1] if len(relative.parts) > 2 else '_root'
            groups[family].append(path)
        populations[logic] = dict(files=sum(map(len, groups.values())), families=len(groups))
        groups = {key: sorted(values, key=lambda p: rank(p.relative_to(root).as_posix()))
                  for key, values in groups.items()}
        families = sorted(groups, key=lambda f: rank(logic + '/' + f))
        selected = []
        depth = 0
        while len(selected) < count:
            changed = False
            for family in families:
                if depth >= len(groups[family]):
                    continue
                path = groups[family][depth]
                data = path.read_bytes()
                status = re.search(rb'\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)', data[:65536])
                selected.append(dict(path=str(path.resolve()), member=path.relative_to(root).as_posix(),
                    logic=logic, family=family, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
                    expected=status[1].decode() if status else 'unknown'))
                changed = True
                if len(selected) == count:
                    break
            if not changed:
                raise ValueError(f'not enough inputs for {logic}')
            depth += 1
        result.extend(selected)
    return dict(seed=seed, population=populations, cases=result,
                policy='round-robin families, seeded SHA-256 rank; no solver outcomes or size cutoff')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    report = select(args.root, {'QF_LIA': 24, 'QF_NIA': 24, 'QF_LRA': 16, 'QF_NRA': 16})
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print({logic: (sum(c['logic'] == logic for c in report['cases']), values) for logic, values in report['population'].items()})


if __name__ == '__main__':
    main()
