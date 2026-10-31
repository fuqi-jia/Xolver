#!/usr/bin/env python3
"""Produce/check complete residue covers of asserted integer polynomial equations.

The checker directly evaluates original SMT-LIB syntax with Python integers.
It does not import Xolver arithmetic or use the solver's coefficient reduction,
component partition or explanations. Every residue tuple must violate a positive
conjunction equality: congruence preservation then excludes every integer model.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from polynomial_mod_certificate import Atom, Budget, Unsupported, numeral, op, positive_literals, program

KIND = 'integer-polynomial-conjunction-residue-cover'


def extract(data):
    equalities, declarations = {}, set()
    budget = Budget()
    for index, assertion, declared in program(data, Budget()):
        declarations.update(declared)
        for path, literal in positive_literals(assertion):
            if op(literal) == '=' and len(literal) == 3:
                # Validate polynomial syntax and the declarations in scope at
                # this assertion, independently of later declarations.
                point = {name: 0 for name in declared}
                evaluate(literal[1], point, budget)
                evaluate(literal[2], point, budget)
                equalities[index, tuple(path)] = literal[1:]
    return equalities, declarations


def evaluate(node, assignment, budget):
    budget.tick()
    if isinstance(node, Atom):
        if node.kind != 'string' and node.text in assignment:
            return assignment[node.text]
        return numeral(node)
    args = [evaluate(child, assignment, budget) for child in node[1:]]
    if op(node) == '+' and len(args) >= 2:
        return sum(args)
    if op(node) == '*' and len(args) >= 2:
        return math.prod(args)
    if op(node) == '-' and args:
        return -args[0] if len(args) == 1 else args[0] - sum(args[1:])
    raise Unsupported('expected integer polynomial operations')


def coverage_size(modulus, variables):
    if (type(modulus) is not int or not 2 <= modulus <= 100 or
            len(variables) > 16 or modulus ** len(variables) > 100000):
        raise Unsupported('residue coverage exceeds certificate limits')
    return modulus ** len(variables)


def produce(data, modulus=3):
    equalities, declared = extract(data)
    variables, references = sorted(declared), sorted(equalities)
    coverage_size(modulus, variables)
    budget, rows = Budget(), []
    for digits in itertools.product(range(modulus), repeat=len(variables)):
        assignment = dict(zip(variables, digits))
        for index, reference in enumerate(references):
            left, right = equalities[reference]
            if (evaluate(left, assignment, budget) - evaluate(right, assignment, budget)) % modulus:
                rows.append(dict(residues=list(digits), violated_equality=index))
                break
        else:
            raise Unsupported('modular relaxation has a satisfying residue assignment')
    return dict(kind=KIND, version=1, input_sha256=hashlib.sha256(data).hexdigest(),
        modulus=modulus, variables=variables,
        equalities=[dict(assertion=index, path=list(path)) for index, path in references], cover=rows)


def verify(data, certificate):
    available, declared = extract(data)
    if (not isinstance(certificate, dict) or certificate.get('kind') != KIND or
            type(certificate.get('version')) is not int or certificate['version'] != 1 or
            certificate.get('input_sha256') != hashlib.sha256(data).hexdigest()):
        raise Unsupported('certificate kind, version or input hash mismatch')
    modulus, variables = certificate.get('modulus'), certificate.get('variables')
    if variables != sorted(declared):
        raise Unsupported('integer declaration coverage mismatch')
    size = coverage_size(modulus, variables)
    references = []
    premises = certificate.get('equalities')
    if not isinstance(premises, list):
        raise Unsupported('invalid equality premises')
    for row in premises:
        if (not isinstance(row, dict) or type(row.get('assertion')) is not int or
                not isinstance(row.get('path'), list) or any(type(i) is not int for i in row['path'])):
            raise Unsupported('invalid equality reference')
        reference = row['assertion'], tuple(row['path'])
        if reference not in available or reference in references:
            raise Unsupported('equality is not an asserted positive conjunction premise')
        references.append(reference)
    if not references:
        raise Unsupported('no equality premises')
    rows = certificate.get('cover')
    if not isinstance(rows, list) or len(rows) != size:
        raise Unsupported('incomplete residue coverage')
    budget = Budget()
    for row, expected in zip(rows, itertools.product(range(modulus), repeat=len(variables))):
        if (not isinstance(row, dict) or row.get('residues') != list(expected) or
                any(type(i) is not int for i in row['residues'])):
            raise Unsupported('duplicate, missing or invalid residue tuple')
        index = row.get('violated_equality')
        if type(index) is not int or not 0 <= index < len(references):
            raise Unsupported('invalid violated equality index')
        left, right = available[references[index]]
        point = dict(zip(variables, expected))
        if (evaluate(left, point, budget) - evaluate(right, point, budget)) % modulus == 0:
            raise Unsupported('residue tuple does not violate the cited equality')
    return dict(result='unsat', checked_residue_classes=size,
        input_sha256=certificate['input_sha256'], modulus=modulus)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('produce', 'check'))
    parser.add_argument('input', type=Path)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--modulus', type=int, default=3)
    args = parser.parse_args()
    data = args.input.read_bytes()
    try:
        if args.command == 'produce':
            certificate = produce(data, args.modulus)
            result = verify(data, certificate)
            args.certificate.write_text(json.dumps(certificate, indent=2)+'\n')
        else:
            result = verify(data, json.loads(args.certificate.read_text()))
        print(json.dumps(result))
        return 0
    except (Unsupported, ValueError, TypeError, KeyError, RecursionError) as error:
        print(json.dumps(dict(result='unsupported', reason=str(error))))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
