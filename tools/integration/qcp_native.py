#!/usr/bin/env python3
"""Export printed native QCP SMT checks without inventing function semantics.

This reads QCP_DEBUG_SMT traces, not generated Rocq goals. It does not replace
QCP's internal solver or establish a C program's correctness. Native result
flags are observations, never trusted expectations for the exported queries.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.integration.qcp import Parser, Term, Unsupported, apply, integer


VARIABLE = re.compile(r'x_[0-9]+\Z')
FUNCTION = re.compile(r'[A-Za-z_][A-Za-z_0-9.\']*\Z')
MAXIMUM = {f'SMT_INT{bits}_MAX': (1 << (bits - 1)) - 1 for bits in (8, 16, 32, 64)}
EVENT = re.compile(r'^\[QCP_DEBUG_SMT\] (Source SMT:|Target SMT:|'
                   r'SingleSmtPropCheck flag=(-?[0-9]+)[^\n]*)\r?$', re.M)


class NativeParser(Parser):
    """The native integer/Boolean printing grammar with explicit UF signatures."""
    def __init__(self, text: str, symbols: dict[str, str], functions: dict[str, int]):
        try:
            super().__init__(text, symbols)
        except Unsupported as error:
            raise Unsupported(str(error).replace('Rocq', 'native SMT')) from error
        self.functions = functions

    def atom(self) -> Term:
        token = self.peek()
        if token == 'NOT':
            self.pop()
            return apply('not', self.typed(self.expression(5), 'Prop'), sort='Prop')
        if token in ('TT', 'FF'):
            self.pop()
            return Term('true' if token == 'TT' else 'false', 'Prop')
        if token in MAXIMUM:
            self.pop()
            return Term(integer(MAXIMUM[token]), 'Int')
        if VARIABLE.fullmatch(token):
            if token in self.functions:
                raise Unsupported('native function/variable name collision')
            self.symbols[token] = 'Int'
            return super().atom()
        if (FUNCTION.fullmatch(token) and self.index + 1 < len(self.tokens)
                and self.tokens[self.index + 1] == '('):
            self.pop(); self.pop('(')
            arguments = []
            if self.peek() != ')':
                while True:
                    arguments.append(self.typed(self.expression(), 'Int'))
                    if self.peek() != ',':
                        break
                    self.pop(',')
            self.pop(')')
            if token in self.symbols or token in MAXIMUM or token in ('TT', 'FF', 'NOT'):
                raise Unsupported('native function/variable name collision')
            previous = self.functions.setdefault(token, len(arguments))
            if previous != len(arguments):
                raise Unsupported('native function arity changed: ' + token)
            symbol = '|' + token + '|'
            return apply(symbol, *arguments, sort='Int') if arguments else Term(symbol, 'Int')
        if token in ('(', '-') or token.isdecimal():
            return super().atom()
        raise Unsupported('unsupported native symbol: ' + token)

    def binary(self, op: str, a: Term, b: Term) -> Term:
        if op not in ('/\\', '\\/', '->', '<->', '=', '<>', '<', '<=', '>', '>=', '+', '-', '*'):
            # Native Omod/Odiv applications are deliberately opaque. Do not
            # inherit Rocq division or remainder semantics from the parser.
            raise Unsupported('unsupported native operator: ' + op)
        return super().binary(op, a, b)


@dataclass(frozen=True)
class NativeCheck:
    source: str
    target: str
    native_flag: int
    source_span: tuple[int, int]
    target_span: tuple[int, int]


def extract_checks(text: str) -> list[NativeCheck]:
    """Pair every observed Source/Target/result; malformed traces fail closed."""
    checks = []
    source_start = target_start = None
    source_span = None
    for marker in EVENT.finditer(text):
        event = marker[1]
        if event == 'Source SMT:':
            if source_start is not None:
                raise Unsupported('native check was not completed before the next source')
            source_start = marker.end()
        elif event == 'Target SMT:':
            if source_start is None or target_start is not None:
                raise Unsupported('native target has no unique source')
            source_span = source_start, marker.start()
            target_start = marker.end()
        else:
            if source_start is None or target_start is None:
                raise Unsupported('native result has no complete source/target pair')
            flag = int(marker[2])
            if flag not in (-1, 0, 1):
                raise Unsupported('unrecognized native result flag')
            target_span = target_start, marker.start()
            source = text[source_span[0]:source_span[1]].strip()
            target = text[target_span[0]:target_span[1]].strip()
            if not source or not target:
                raise Unsupported('native source or target is empty')
            if len(checks) >= 10000:
                raise Unsupported('native check allocation exhausted')
            checks.append(NativeCheck(source, target, flag, source_span, target_span))
            source_start = target_start = source_span = None
    if source_start is not None or target_start is not None:
        raise Unsupported('truncated native check')
    if not checks:
        raise Unsupported('trace has no captured native SMT checks')
    return checks


def _nonlinear(term: Term) -> bool:
    constants = {}
    pending = [(term, False)]
    while pending:
        node, visited = pending.pop()
        if id(node) in constants:
            continue
        if not visited:
            pending.append((node, True))
            pending.extend((child, False) for child in node.args)
            continue
        if node.op == '*' and sum(not constants[id(a)] for a in node.args) > 1:
            return True
        constants[id(node)] = node.smt.isdecimal() or (
            node.op in ('+', '-', '*') and all(constants[id(a)] for a in node.args))
    return False


def query(check: NativeCheck) -> tuple[str, dict]:
    symbols, functions = {}, {}
    source = NativeParser(check.source, symbols, functions).parse()
    target = NativeParser(check.target, symbols, functions).parse()
    if source.sort != 'Prop' or target.sort != 'Prop':
        raise Unsupported('native source and target must be propositions')
    nonlinear = _nonlinear(source) or _nonlinear(target)
    logic = 'QF_' + ('UF' if functions else '') + ('NIA' if nonlinear else 'LIA')
    lines = ['(set-logic ' + logic + ')']
    lines += [f'(declare-const |{name}| Int)' for name in sorted(symbols)]
    lines += [f"(declare-fun |{name}| ({' '.join(['Int'] * arity)}) Int)"
              for name, arity in sorted(functions.items())]
    lines += [f'(assert {source.smt})', f'(assert (not {target.smt}))', '(check-sat)', '(exit)', '']
    return '\n'.join(lines), dict(logic=logic, variables=sorted(symbols),
        functions={name: dict(arguments=['Int'] * arity, result='Int', semantics='uninterpreted')
                   for name, arity in sorted(functions.items())})


def export_trace(trace: Path, output: Path) -> dict:
    raw = trace.read_bytes()
    if len(raw) > 16 * 1024**2:
        raise Unsupported('native trace byte budget exhausted')
    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError as error:
        raise Unsupported('native trace is not UTF-8') from error
    checks = extract_checks(text)
    output.mkdir(parents=True, exist_ok=False)
    report = dict(schema='qcp-native-smt-trace/1', trace_sha256=hashlib.sha256(raw).hexdigest(),
        captured_checks=len(checks), queries=[], unsupported=[], program_verified=False,
        internal_qcp_queries_total=None, offset_unit='Unicode code points',
        generation_completion_marker=text.rstrip().endswith('Successfully finished symbolic execution'),
        boundary='Standalone refutations of printed native Source SMT / Target SMT pairs. '
                 'Every captured occurrence is retained; no deduplication. Native flags are '
                 'untrusted observations. Printed function applications are uninterpreted, '
                 'without added arithmetic/GCD axioms. This is capture/replay, not an internal '
                 'solver replacement, proof of a C program, or complete native-call census.')
    for ordinal, check in enumerate(checks):
        row = dict(ordinal=ordinal, native_flag=check.native_flag,
                   source=check.source, target=check.target,
                   source_span=list(check.source_span), target_span=list(check.target_span))
        try:
            script, details = query(check)
            name = f'query-{ordinal:05d}.smt2'
            (output / name).write_text(script)
            row.update(file=name, sha256=hashlib.sha256(script.encode()).hexdigest(), **details)
            report['queries'].append(row)
        except Unsupported as error:
            row['reason'] = str(error)
            report['unsupported'].append(row)
    report['unique_queries'] = len({row['sha256'] for row in report['queries']})
    (output / 'manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trace', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = export_trace(args.trace, args.output)
    print(json.dumps(dict(captured_checks=result['captured_checks'], exported=len(result['queries']),
                          unsupported=len(result['unsupported']), unique_queries=result['unique_queries'],
                          program_verified=False)))
    return int(bool(result['unsupported']))


if __name__ == '__main__':
    raise SystemExit(main())
