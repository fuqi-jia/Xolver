#!/usr/bin/env python3
"""Check an original integer query using a finite polynomial-modulo certificate.

Only positive conjunctions of assertions are searched for not(P(x) mod m = 0).
For nonzero constant m, checking every residue class proves this literal false
for ALL integers, by preservation of congruence under integer +, - and *.
Parsing is shared with the standalone proof tools; arithmetic evaluation uses
Python integers and never calls Xolver or its polynomial kernel.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'proof'))
from isabelle_pa import Atom, Unsupported, parse, symbol


def op(node):
    return (node[0].text if isinstance(node, list) and node and
            isinstance(node[0], Atom) and node[0].kind == 'symbol' else None)


def numeral(node):
    if isinstance(node, Atom) and node.kind == 'symbol' and re.fullmatch(r'0|[1-9][0-9]*', node.text):
        return int(node.text)
    if op(node) == '-' and len(node) == 2:
        return -numeral(node[1])
    raise Unsupported('expected an integer numeral')


class Budget:
    def __init__(self):
        self.remaining = 1000000

    def tick(self):
        self.remaining -= 1
        if self.remaining < 0:
            raise Unsupported('certificate construction limit exceeded')


def expand(node, env, budget):
    budget.tick()
    if isinstance(node, Atom):
        if node.kind == 'symbol' and (re.fullmatch(r'0|[1-9][0-9]*', node.text) or
                                      node.text in ('true', 'false')):
            return node
        return env.get(node.text, node) if node.kind != 'string' else node
    if not isinstance(node, list) or not node:
        raise Unsupported('empty or invalid term')
    if op(node) == 'let':
        if len(node) != 3 or not isinstance(node[1], list):
            raise Unsupported('invalid let')
        additions = {}
        for binding in node[1]:
            if (not isinstance(binding, list) or len(binding) != 2 or
                    not isinstance(binding[0], Atom) or binding[0].kind == 'string'):
                raise Unsupported('invalid simultaneous let binding')
            name = symbol(binding[0])
            if name in additions:
                raise Unsupported('duplicate let binding')
            # SMT-LIB let bindings are simultaneous. Returned expansions must
            # not be expanded again in the new environment (variable capture).
            additions[name] = expand(binding[1], env, budget)
        return expand(node[2], {**env, **additions}, budget)
    return [node[0], *(expand(child, env, budget) for child in node[1:])]


def program(data, budget):
    declarations, assertions = set(), []
    checked, exited, logic = False, False, False
    if len(data) > 4 * 1024**2:
        raise Unsupported('input too large')
    for index, command in enumerate(parse(data.decode('utf-8'))):
        budget.tick()
        kind = op(command)
        if exited or (checked and kind not in ('exit', 'set-info', 'set-option')):
            raise Unsupported('only one query without later state changes is supported')
        if kind in ('set-info', 'set-option'):
            continue
        if kind == 'set-logic' and len(command) == 2:
            if logic or command[1] not in (Atom('QF_NIA'), Atom('QF_LIA'), Atom('ALL')):
                raise Unsupported('expected an integer arithmetic logic')
            logic = True
        elif kind in ('declare-const', 'declare-fun'):
            if (len(command) != (3 if kind == 'declare-const' else 4) or
                    (kind == 'declare-fun' and command[2] != []) or
                    command[-1] != Atom('Int') or not isinstance(command[1], Atom) or
                    command[1].kind == 'string' or command[1].text in declarations):
                raise Unsupported('expected unique nullary integer declarations')
            declarations.add(symbol(command[1]))
        elif kind == 'assert' and len(command) == 2:
            assertions.append((index, expand(command[1], {}, budget), frozenset(declarations)))
        elif kind == 'check-sat' and len(command) == 1:
            checked = True
        elif kind == 'exit' and len(command) == 1 and checked:
            exited = True
        else:
            raise Unsupported('unsupported stateful command or declaration')
    if not checked:
        raise Unsupported('missing check-sat')
    return assertions


def positive_literals(node, path=()):
    if op(node) == 'and':
        for index, child in enumerate(node[1:], 1):
            yield from positive_literals(child, (*path, index))
    else:
        yield path, node


class Polynomial:
    def __init__(self, declarations, budget):
        self.declarations, self.budget, self.variable = declarations, budget, None

    def read(self, node):
        self.budget.tick()
        if isinstance(node, Atom):
            if node.kind == 'symbol' and re.fullmatch(r'0|[1-9][0-9]*', node.text):
                return {0: int(node.text)}
            if node.kind == 'string' or node.text not in self.declarations:
                raise Unsupported('undeclared or non-integer polynomial variable')
            if self.variable not in (None, node.text):
                raise Unsupported('polynomial is not univariate')
            self.variable = node.text
            return {1: 1}
        kind = op(node)
        if kind not in ('+', '-', '*') or len(node) < (2 if kind == '-' else 3):
            raise Unsupported('expected integer polynomial operations')
        args = [self.read(child) for child in node[1:]]
        if kind in ('+', '-'):
            result = {}
            for index, arg in enumerate(args):
                sign = -1 if kind == '-' and (index > 0 or len(args) == 1) else 1
                for degree, coefficient in arg.items():
                    self.budget.tick()
                    result[degree] = result.get(degree, 0) + sign * coefficient
        else:
            result = {0: 1}
            for arg in args:
                product = {}
                for left, a in result.items():
                    for right, b in arg.items():
                        self.budget.tick()
                        if left + right > 64:
                            raise Unsupported('polynomial degree exceeds certificate limit')
                        product[left + right] = product.get(left + right, 0) + a * b
                result = product
        return {degree: coefficient for degree, coefficient in result.items() if coefficient}


def cores(data):
    budget = Budget()
    assertions = program(data, budget)
    for assertion, body, declarations in assertions:
        for path, literal in positive_literals(body):
            if op(literal) != 'not' or len(literal) != 2:
                continue
            equality = literal[1]
            if op(equality) != '=' or len(equality) != 3:
                continue
            for term, zero in ((equality[1], equality[2]), (equality[2], equality[1])):
                try:
                    if numeral(zero) != 0 or op(term) != 'mod' or len(term) != 3:
                        continue
                    modulus = abs(numeral(term[2]))
                    if not 0 < modulus <= 4096:
                        continue  # mod by zero is an unconstrained total function
                    reader = Polynomial(declarations, budget)
                    coefficients = reader.read(term[1])
                    dense = [coefficients.get(i, 0) for i in range(max(coefficients, default=0) + 1)]
                    yield dict(assertion=assertion, path=list(path), modulus=modulus,
                               variable=reader.variable, coefficients=dense, term=term[1])
                except Unsupported:
                    continue


def evaluate(node, variable, residue):
    """Independent direct AST evaluation, separate from coefficient extraction."""
    if isinstance(node, Atom):
        if node.kind == 'symbol' and re.fullmatch(r'0|[1-9][0-9]*', node.text):
            return int(node.text)
        return residue if node.kind != 'string' and node.text == variable else numeral(node)
    values = [evaluate(child, variable, residue) for child in node[1:]]
    if op(node) == '+':
        return sum(values)
    if op(node) == '*':
        return math.prod(values)
    if op(node) == '-':
        return -values[0] if len(values) == 1 else values[0] - sum(values[1:])
    raise Unsupported('unsupported arithmetic evaluation')


def produce(data):
    for core in cores(data):
        m, coefficients = core['modulus'], core['coefficients']
        table = [sum(c * pow(r, i, m) for i, c in enumerate(coefficients)) % m for r in range(m)]
        if any(table):
            continue
        return dict(kind='integer-polynomial-mod-zero', version=1,
                    input_sha256=hashlib.sha256(data).hexdigest(),
                    **{k: v for k, v in core.items() if k != 'term'}, residues=table)
    raise Unsupported('no supported universally false modular literal found')


def verify(data, certificate):
    if (not isinstance(certificate, dict) or
            certificate.get('kind') != 'integer-polynomial-mod-zero' or certificate.get('version') != 1 or
            certificate.get('input_sha256') != hashlib.sha256(data).hexdigest()):
        raise Unsupported('certificate kind, version or input hash mismatch')
    for core in cores(data):
        if any(certificate.get(key) != value for key, value in core.items() if key != 'term'):
            continue
        table, m = certificate.get('residues'), core['modulus']
        if not isinstance(table, list) or len(table) != m:
            raise Unsupported('incomplete residue coverage')
        for residue, claimed in enumerate(table):
            # Horner evaluation and direct source-AST evaluation must agree.
            value = 0
            for coefficient in reversed(core['coefficients']):
                value = value * residue + coefficient
            if (type(claimed) is not int or claimed != 0 or value % m != claimed or
                    evaluate(core['term'], core['variable'], residue) % m != claimed):
                raise Unsupported('invalid residue witness')
        return dict(status='checked-unsat', input_sha256=certificate['input_sha256'],
                    assertion=core['assertion'], path=core['path'], checked_residues=m)
    raise Unsupported('certificate does not identify a supported original assertion')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('produce', 'check'))
    parser.add_argument('input', type=Path)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    try:
        data = args.input.read_bytes()
        if args.action == 'produce':
            args.certificate.write_text(json.dumps(produce(data), indent=2) + '\n')
        else:
            print(json.dumps(verify(data, json.loads(args.certificate.read_text()))))
    except (ValueError, KeyError, TypeError, RecursionError) as error:
        raise SystemExit(str(error))


if __name__ == '__main__':
    main()
