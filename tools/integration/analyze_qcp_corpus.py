#!/usr/bin/env python3
"""Measure export coverage and alpha-identical overlap, retaining every failure."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re


TOKENS = re.compile(r'"(?:""|[^"])*"|\|[^|]*\||[()]|[^\s()]+')


def fingerprint(script):
    # The accepted source profile exports only flat Z/bool declarations and
    # assertions. This erases free-variable spelling, not constants or context.
    tokens = TOKENS.findall(re.sub(r';[^\n]*', '', script))
    forms = []
    stack = []
    for token in tokens:
        if token == '(':
            stack.append([])
        elif token == ')':
            form = stack.pop()
            if stack:
                stack[-1].append(form)
            else:
                forms.append(form)
        else:
            if not stack:
                raise ValueError('token outside an expression')
            stack[-1].append(token)
    if stack:
        raise ValueError('unclosed expression')
    declarations = {f[1]: f[2] for f in forms if f and f[0] == 'declare-const'}
    names, sorts = {}, []
    def normalize(expr):
        if isinstance(expr, list):
            return [normalize(c) for c in expr]
        if expr in declarations:
            if expr not in names:
                names[expr] = 'v' + str(len(names))
                sorts.append(declarations[expr])
            return names[expr]
        return expr
    assertions = [normalize(f[1]) for f in forms if f and f[0] == 'assert']
    return hashlib.sha256(json.dumps([sorts, assertions], separators=(',', ':')).encode()).hexdigest()


def queries(root):
    report = json.loads((root / 'manifest.json').read_text())
    for query in report['queries']:
        path = root / query['file']
        if hashlib.sha256(path.read_bytes()).hexdigest() != query['query_sha256']:
            raise ValueError('query hash mismatch')
        yield query, path, fingerprint(path.read_text())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--corpus', type=Path, required=True)
    p.add_argument('--development', type=Path, action='append', default=[])
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    development = {key for root in args.development for _, _, key in queries(root)}
    seen, cases = set(), []
    overlap = duplicates = 0
    rows = list(queries(args.corpus))
    for query, path, key in rows:
        if key in development:
            overlap += 1
        elif key in seen:
            duplicates += 1
        else:
            cases.append(dict(path=str(path.resolve()), sha256=query['query_sha256'],
                family=str(Path(query['source']).parent), logic='QCP-pure',
                alpha_hash=key, expected='unknown'))
        seen.add(key)
    cases.sort(key=lambda c: hashlib.sha256(('20261025:'+c['alpha_hash']).encode()).hexdigest())
    for row in cases[:24]:
        row['repetitions'] = 3
    manifest = json.loads((args.corpus / 'manifest.json').read_text())
    report = dict(cases=cases, raw_queries=len(rows), unique_alpha_queries=len(seen),
        overlap_with_development=overlap, duplicate_novel_occurrences=duplicates,
        programs=len(manifest.get('programs', [])),
        generation= dict(collections.Counter(str(x['returncode']) for x in manifest.get('programs', []))),
        generated_definitions=sum(x.get('goals', 0) for x in manifest.get('programs', [])),
        unsupported_definitions=sum(x.get('unsupported', 0) for x in manifest.get('programs', [])),
        criterion='unseen program families; exclude alpha-identical development queries; no solver outcomes used',
        limitation='alpha-normalization is not complete semantic equivalence checking')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('cases',)}))


if __name__ == '__main__':
    main()
