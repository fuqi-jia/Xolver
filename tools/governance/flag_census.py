#!/usr/bin/env python3
"""Inventory live runtime controls, with source locations and reader semantics.

This is an audit report, not an allowlist. Classification is advisory: a
diagnostic reader can still control a correctness-sensitive branch.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
TOKENS = re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', re.S)
READ = re.compile(
    r'(?:(?P<raw>(?:std::)?getenv)|(?:xolver::)?env::(?P<typed>get|flag|diag|paramInt|paramLong|paramDouble))'
    r'\s*\(\s*"(?P<name>[A-Z][A-Z0-9_]*)"')
TYPED_CALL = re.compile(
    r'(?<!\w)(?:(?:xolver::)?config::)?read\s*<\s*'
    r'(?:(?:xolver::)?config::)?ReadKind::(?P<kind>\w+)\s*>\s*\(')
LITERAL_NAME = re.compile(r'\s*"(?P<name>[A-Z][A-Z0-9_]*)"(?=\s*[,)])')
OLD_KEY_READ = re.compile(
    r'(?<!\w)(?:(?:xolver::)?config::)?read\s*\(\s*'
    r'(?:(?:xolver::)?config::)?control::(\w+)')


def code_only(source: str) -> str:
    return TOKENS.sub(lambda m: re.sub(r'[^\n]', ' ', m[0])
                      if m[0].startswith(('//', '/*')) else m[0], source)


def category(name: str, readers: set[str]) -> str:
    if re.search(r'VALIDAT|SAFE|FIREWALL|STRICT', name):
        return 'correctness-review'
    if re.search(r'DIAG|PROF|TRACE|DUMP|STATS|_LOG$|_SAMPLE$', name):
        return 'diagnostic-review'
    if readers & {'paramInt', 'paramLong', 'paramDouble', 'Int', 'Long', 'Double',
                  'Capacity', 'Period', 'Moduli'}:
        return 'numeric-or-boolean-review'
    if re.search(r'ENGINE|MCSAT|CDCAC|BITBLAST|LOCALSEARCH|PORTFOLIO|STRAT_', name):
        return 'strategy-review'
    return 'heuristic-or-preprocessing-review'


def inventory(root: Path = ROOT) -> dict:
    controls = {}
    dynamic = []
    catalog = json.loads((root / "src/base/controls.json").read_text())
    for directory in ('src', 'include', 'app', 'tools'):
        for path in sorted((root / directory).rglob('*')):
            if path.suffix not in ('.cpp', '.h'):
                continue
            code = code_only(path.read_text())
            # Locate calls outside quoted examples; keep the original offsets
            # so the first argument can still be checked as a string literal.
            call_code = TOKENS.sub(lambda m: re.sub(r'[^\n]', ' ', m[0]), code)
            relative = path.relative_to(root).as_posix()
            for match in TYPED_CALL.finditer(call_code):
                literal = LITERAL_NAME.match(code, match.end())
                if not literal:
                    dynamic.append({'path': relative, 'line': code.count('\n', 0, match.start()) + 1,
                                    'typed_kind': match['kind'],
                                    'argument': code[match.end():match.end() + 100]})
                    continue
                name, kind = literal['name'], match['kind']
                controls.setdefault(name, []).append({
                    'path': relative, 'line': code.count('\n', 0, match.start()) + 1,
                    'reader': kind,
                    'semantics': {
                        'Presence': 'presence (even 0 enables)',
                        'Flag': 'nonempty and first character != 0; caller default',
                        'Boolean': 'canonical case-insensitive Boolean; caller default on invalid/empty',
                        'Path': 'owned filesystem path; caller fallback on missing/empty',
                        'ProfilePath': 'optional profile destination; true selects default path',
                        'Period': 'sampling period; zero disables; true or 1 selects default',
                        'Capacity': 'entry capacity; zero is unbounded; true selects default',
                        'Moduli': 'validated distinct integer list in [2,100]; whole-list fallback',
                        'Projection': 'typed automatic/Collins/Lazard strategy'
                    }.get(kind, 'checked numeric conversion with caller default'),
                })
            for match in OLD_KEY_READ.finditer(call_code):
                dynamic.append({'path': relative, 'line': code.count('\n', 0, match.start()) + 1,
                                'typed_kind': 'retired-catalog-key', 'argument': match[1]})
            for match in READ.finditer(code):
                name = match['name']
                reader = 'getenv' if match['raw'] else match['typed']
                controls.setdefault(name, []).append({
                    'path': relative, 'line': code.count('\n', 0, match.start()) + 1,
                    'reader': reader,
                    'semantics': {'diag': 'presence (even 0 enables)',
                                  'flag': 'nonempty and first character != 0; caller default',
                                  'get': 'query snapshot; call-site-defined parsing',
                                  'getenv': 'process environment; call-site-defined'}.get(reader, 'numeric with caller default'),
                })
            for m in re.finditer(r'(?:\bgetenv|\benv::get)\s*\(\s*([^"\s][^)]*)\)', code):
                dynamic.append({'path': relative, 'line': code.count('\n', 0, m.start()) + 1,
                                'argument': m[1].strip()})
    entries = []
    for name, sites in sorted(controls.items()):
        readers = {s['reader'] for s in sites}
        entries.append({'name': name, 'category': category(name, readers), 'sites': sites,
                        'mixed_reader_semantics': len(readers) > 1})
    return {'schema': 'xolver-runtime-control-inventory/3',
            'unique_controls': len(entries), 'literal_read_sites': sum(len(x['sites']) for x in entries),
            'categories': dict(sorted(Counter(x['category'] for x in entries).items())),
            'controls': entries, 'dynamic_reads': dynamic,
            'declared_controls': len(catalog["controls"]),
            'legacy_text_controls': sum(any(r["kind"] == "Text" for r in e["reads"])
                                        for e in catalog["controls"])}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', nargs='?', default=str(ROOT / 'docs/audit/FLAGS.md'))
    args = parser.parse_args()
    data = inventory()
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.with_suffix('.json').write_text(json.dumps(data, indent=2) + '\n')
    lines = ['# Live runtime controls', '',
             'Generated by `tools/governance/flag_census.py`. Comments are excluded.', '',
             '**Categories require review; they are not correctness guarantees.**', '',
             f"{data['unique_controls']} named controls at {data['literal_read_sites']} literal read sites.", '',
             '| Control | Review category | Readers | Sites |', '|---|---|---|---|']
    for entry in data['controls']:
        readers = ', '.join(sorted({s['reader'] for s in entry['sites']}))
        sites = ', '.join(f"{s['path']}:{s['line']}" for s in entry['sites'])
        lines.append(f"| `{entry['name']}` | {entry['category']} | {readers} | {sites} |")
    lines += ['', 'Dynamic reads and exact reader semantics are in the accompanying JSON.',
              'Baked CLI defaults and strategy writes must also be reviewed at their write sites.', '']
    out.write_text('\n'.join(lines))
    print(f"{data['unique_controls']} controls / {data['literal_read_sites']} sites -> {out}")


if __name__ == '__main__':
    main()
