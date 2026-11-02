#!/usr/bin/env python3
"""Check an exact polynomial identity whose asserted equalities imply 0 > 0.

Certificates combine unconditional numeric equalities with polynomial factors.
Their sum must equal a provably positive expression built from positive root
facts, nonnegative even powers, addition and multiplication. No SMT solver is
called, and no asserted status or benchmark name participates in checking.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

from isabelle_pa import Atom, parse


class Checker:
    def __init__(self, source, certificate):
        self.certificate = certificate
        if hashlib.sha256(source.encode()).hexdigest() != certificate['input_sha256']:
            raise ValueError('input hash mismatch')
        self.variables, self.roots, self.positive = set(), [], set()
        commands = parse(source)
        symbols, pending = set(), list(commands)
        while pending:
            item = pending.pop()
            if isinstance(item, list):
                pending.extend(item)
            elif isinstance(item, Atom) and item.kind != 'string':
                symbols.add(item.text)
        checked_query = False
        for command in commands:
            if not isinstance(command, list) or not command:
                continue
            op = command[0].text
            if op not in ('declare-const', 'declare-fun', 'assert', 'check-sat',
                          'set-info', 'set-logic', 'exit'):
                raise ValueError('unsupported input command or scope')
            if op == 'check-sat':
                if checked_query:
                    raise ValueError('multiple queries are unsupported')
                checked_query = True
            if checked_query and op in ('assert', 'declare-const', 'declare-fun'):
                raise ValueError('input context changes after query')
            if op == 'declare-const' and command[2].text in ('Int', 'Real'):
                self.variables.add(command[1].text)
            elif op == 'declare-fun' and command[2] == [] and command[3].text in ('Int', 'Real'):
                self.variables.add(command[1].text)
            elif op == 'assert':
                pending = [command[1]]
                while pending:
                    root = pending.pop()
                    if isinstance(root, list) and root and root[0] == Atom('and'):
                        pending.extend(reversed(root[1:]))
                    else:
                        self.roots.append(root)
        self.definitions = {}
        for name, expression in certificate.get('definitions', {}).items():
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) or name in symbols:
                raise ValueError('certificate definition shadows input or reserved syntax')
            self.definitions[name] = self.expression(expression)
        self.work = 0
        for root in self.roots:
            if not isinstance(root, list) or len(root) != 3 or root[0].text not in ('<', '>'):
                continue
            try:
                difference = self.add(self.polynomial(root[1]), self.polynomial(root[2]), -1)
            except ValueError:
                continue
            if len(difference) != 1:
                continue
            monomial, coefficient = next(iter(difference.items()))
            if len(monomial) == 1 and monomial[0][1] == 1:
                if (root[0].text == '>' and coefficient > 0) or (root[0].text == '<' and coefficient < 0):
                    self.positive.add(monomial[0][0])

    @staticmethod
    def expression(text):
        nodes = parse(text)
        if len(nodes) != 1:
            raise ValueError('expected one arithmetic expression')
        return nodes[0]

    @staticmethod
    def add(left, right, scale=1):
        result = dict(left)
        for monomial, coefficient in right.items():
            value = result.get(monomial, 0) + coefficient * scale
            if value:
                result[monomial] = value
            else:
                result.pop(monomial, None)
        return result

    def multiply(self, left, right):
        self.work += len(left) * len(right)
        if self.work > 1000000:
            raise ValueError('certificate work limit exceeded')
        result = {}
        for a, x in left.items():
            for b, y in right.items():
                powers = dict(a)
                for variable, exponent in b:
                    powers[variable] = powers.get(variable, 0) + exponent
                monomial = tuple(sorted(powers.items()))
                result[monomial] = result.get(monomial, 0) + x * y
        return {m: c for m, c in result.items() if c}

    def polynomial(self, node, expanding=frozenset()):
        if isinstance(node, Atom):
            if node.text in self.variables:
                return {((node.text, 1),): Fraction(1)}
            if node.text in self.definitions:
                if node.text in expanding:
                    raise ValueError('cyclic certificate definitions')
                return self.polynomial(self.definitions[node.text], expanding | {node.text})
            if node.kind != 'symbol':
                raise ValueError('unsupported numeric atom')
            value = Fraction(node.text)
            return {(): value} if value else {}
        op, children = node[0].text, node[1:]
        if op in ('+', '-') and children:
            result = self.polynomial(children[0], expanding)
            if op == '-' and len(children) == 1:
                return {m: -c for m, c in result.items()}
            for child in children[1:]:
                result = self.add(result, self.polynomial(child, expanding), -1 if op == '-' else 1)
            return result
        if op == '*' and children:
            result = {(): Fraction(1)}
            for child in children:
                result = self.multiply(result, self.polynomial(child, expanding))
            return result
        if op == '^' and len(children) == 2 and isinstance(children[1], Atom):
            exponent = int(children[1].text)
            if not 0 <= exponent <= 100:
                raise ValueError('unsupported exponent')
            result, base = {(): Fraction(1)}, self.polynomial(children[0], expanding)
            while exponent:
                if exponent & 1:
                    result = self.multiply(result, base)
                exponent >>= 1
                if exponent:
                    base = self.multiply(base, base)
            return result
        if op == '/' and len(children) == 2:
            denominator = self.polynomial(children[1], expanding)
            if set(denominator) != {()}:
                raise ValueError('division requires nonzero rational denominator')
            return {m: c / denominator[()] for m, c in self.polynomial(children[0], expanding).items()}
        raise ValueError('unsupported polynomial expression')

    def sign(self, node, expanding=frozenset()):
        # 0 = unknown, 1 = nonnegative, 2 = strictly positive.
        if isinstance(node, Atom):
            if node.text in self.positive:
                return 2
            if node.text in self.variables:
                return 0
            if node.text in self.definitions:
                if node.text in expanding:
                    raise ValueError('cyclic certificate definitions')
                return self.sign(self.definitions[node.text], expanding | {node.text})
            value = Fraction(node.text)
            return 2 if value > 0 else 1 if value == 0 else 0
        op, children = node[0].text, node[1:]
        if op == '^' and len(children) == 2:
            exponent = int(children[1].text)
            if exponent == 0:
                return 2
            if exponent > 0:
                sign = self.sign(children[0], expanding)
                return sign if exponent % 2 else 2 if sign == 2 else 1
        if op in ('+', '*') and children:
            signs = [self.sign(c, expanding) for c in children]
            if all(signs):
                return (2 if any(s == 2 for s in signs) else 1) if op == '+' else min(signs)
        return 0

    def check(self):
        combined = {}
        for item in self.certificate['multipliers']:
            index = item['premise']
            if not isinstance(index, int) or not 0 <= index < len(self.roots):
                raise ValueError('invalid premise index')
            root = self.roots[index]
            if not isinstance(root, list) or len(root) != 3 or root[0] != Atom('='):
                raise ValueError('multiplier premise must be an unconditional equality')
            equation = self.add(self.polynomial(root[1]), self.polynomial(root[2]), -1)
            combined = self.add(combined, self.multiply(equation, self.polynomial(self.expression(item['factor']))))
        positive = self.expression(self.certificate['positive_expression'])
        if combined != self.polynomial(positive):
            raise ValueError('polynomial identity mismatch')
        if self.sign(positive) != 2:
            raise ValueError('identity right hand side is not proved strictly positive')
        return dict(checked=True, premises=len(self.certificate['multipliers']), terms=len(combined), work=self.work)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(Checker(args.input.read_text(), json.loads(args.certificate.read_text())).check()))


if __name__ == '__main__':
    main()
