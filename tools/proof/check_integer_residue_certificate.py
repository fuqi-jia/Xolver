#!/usr/bin/env python3
"""Check finite residue refutations of integer SMT-LIB assertions.

For each tuple modulo the certificate modulus, the abstract evaluator must
falsify an original assertion. Polynomial residues overapproximate integers;
a mod expression is exact only for a positive constant divisor that divides
the enumerated modulus (or an already exact argument). Equal residues alone
never prove integer equality. Unsupported syntax fails closed.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parent))
from isabelle_pa import Atom, parse

class Unsupported(Exception):
    pass

def name(x):
    if not isinstance(x, Atom) or x.kind == 'string':
        raise Unsupported('expected symbol')
    return x.text

def integer(v, exact=False):
    return ('Int', v, exact)

def boolean(v):
    return ('Bool', v)

def truth(v):
    if v[0] != 'Bool':
        raise Unsupported('expected boolean')
    return v[1]

def num(v):
    if v[0] != 'Int':
        raise Unsupported('expected integer')
    return (v[1], v[2])

def conjunction(vs):
    return False if False in vs else None if None in vs else True

def disjunction(vs):
    return True if True in vs else None if None in vs else False

def eq(a, b, m):
    if a[0] != b[0]:
        raise Unsupported('sort mismatch')
    if a[0] == 'Bool':
        return None if a[1] is None or b[1] is None else a[1] == b[1]
    (x, xe) = num(a)
    (y, ye) = num(b)
    if x is None or y is None:
        return None
    if xe and ye:
        return x == y
    return False if x % m != y % m else None

def evaluate(node, env, m):
    if isinstance(node, Atom):
        if node.kind == 'string':
            raise Unsupported('string literal')
        # Numerals are lexical literals. A quoted declaration such as |0|
        # denotes a symbol and cannot change the meaning of the literal 0.
        if node.kind != 'quoted':
            if re.fullmatch(r'0|[1-9][0-9]*', node.text):
                return integer(int(node.text), True)
            if node.text[:1] in '0123456789' or node.text.startswith(('#b', '#x')):
                raise Unsupported('unsupported numeric literal')
        if node.text in env:
            return env[node.text]
        if node.kind != 'quoted' and node.text in ('true', 'false'):
            return boolean(node.text == 'true')
        if node.kind == 'quoted':
            raise Unsupported('unknown quoted symbol')
        raise Unsupported('unknown atom')
    if not isinstance(node, list) or not node:
        raise Unsupported('malformed term')
    op = name(node[0])
    if op == 'let':
        if len(node) != 3 or not isinstance(node[1], list):
            raise Unsupported('malformed let')
        extended = dict(env)
        seen = set()
        for binding in node[1]:
            if not isinstance(binding, list) or len(binding) != 2:
                raise Unsupported('malformed let binding')
            symbol = name(binding[0])
            if symbol in seen:
                raise Unsupported('duplicate let binding')
            seen.add(symbol)
            extended[symbol] = evaluate(binding[1], env, m)
        return evaluate(node[2], extended, m)
    if op == '!':
        if len(node) < 2:
            raise Unsupported('malformed annotation')
        return evaluate(node[1], env, m)
    args = [evaluate(x, env, m) for x in node[1:]]
    if op in ('+', '-', '*'):
        if not args:
            raise Unsupported('empty arithmetic application')
        ns = [num(v) for v in args]
        if any((v is None for (v, e) in ns)):
            return integer(None)
        exact = all((e for (v, e) in ns))
        if op == '+':
            value = sum((v for (v, e) in ns))
        elif op == '*':
            value = 1
            for (v, e) in ns:
                value *= v
        elif len(ns) == 1:
            value = -ns[0][0]
        else:
            value = ns[0][0] - sum((v for (v, e) in ns[1:]))
        return integer(value if exact else value % m, exact)
    if op == 'mod':
        if len(args) != 2:
            raise Unsupported('mod arity')
        (a, ae) = num(args[0])
        (d, de) = num(args[1])
        if not de or d is None or d <= 0:
            raise Unsupported('nonpositive or symbolic modulus')
        if a is None or (not ae and m % d):
            return integer(None)
        return integer(a % d, True)
    if op in ('and', 'or', 'not', '=>', 'xor'):
        vs = [truth(x) for x in args]
        if op == 'and':
            return boolean(conjunction(vs))
        if op == 'or':
            return boolean(disjunction(vs))
        if op == 'not':
            if len(vs) != 1:
                raise Unsupported('not arity')
            return boolean(None if vs[0] is None else not vs[0])
        if op == '=>':
            if len(vs) < 2:
                raise Unsupported('implication arity')
            a = conjunction(vs[:-1])
            return boolean(disjunction([None if a is None else not a, vs[-1]]))
        if len(vs) < 2:
            raise Unsupported('xor arity')
        return boolean(None if None in vs else bool(sum(vs) % 2))
    if op in ('=', 'distinct'):
        if len(args) < 2:
            raise Unsupported('comparison arity')
        if op == '=':
            return boolean(conjunction([eq(args[0], v, m) for v in args[1:]]))
        es = [eq(args[i], args[j], m) for i in range(len(args)) for j in range(i)]
        return boolean(conjunction([None if v is None else not v for v in es]))
    if op in ('<', '<=', '>', '>='):
        if len(args) < 2:
            raise Unsupported('order arity')
        ns = [num(v) for v in args]
        results = []
        for ((a, ae), (b, be)) in zip(ns, ns[1:]):
            results.append(None if not ae or not be else {'<': a < b, '<=': a <= b, '>': a > b, '>=': a >= b}[op])
        return boolean(conjunction(results))
    raise Unsupported('unsupported operation')

def problem(source):
    nodes = parse(source)
    if sum((name(c[0]) == 'check-sat' for c in nodes)) != 1:
        raise Unsupported('exactly one check-sat is required')
    (variables, roots, seen_check) = ([], [], False)
    for command in nodes:
        op = name(command[0])
        if op in ('check-sat', 'get-model', 'exit') and len(command) != 1:
            raise Unsupported('query command arity')
        if op in ('get-model', 'exit') and not seen_check:
            raise Unsupported('response or exit before query')
        if seen_check and op not in ('get-model', 'exit', 'set-info', 'set-option'):
            raise Unsupported('commands after query')
        if op == 'check-sat':
            seen_check = True
        if op in ('set-logic', 'set-option', 'set-info', 'check-sat', 'get-model', 'exit'):
            continue
        if op == 'declare-fun':
            if len(command) != 4 or command[2] or name(command[3]) != 'Int':
                raise Unsupported('noninteger or nonconstant declaration')
            variables.append(name(command[1]))
        elif op == 'declare-const':
            if len(command) != 3 or name(command[2]) != 'Int':
                raise Unsupported('noninteger declaration')
            variables.append(name(command[1]))
        elif op == 'assert':
            if len(command) != 2:
                raise Unsupported('assert arity')
            roots.append(command[1])
        else:
            raise Unsupported('unsupported command')
    if len(set(variables)) != len(variables):
        raise Unsupported('duplicate declaration')
    return (variables, roots)

def residue_tuples(modulus, arity):
    """Enumerate without a modulus-sized allocation from an untrusted certificate."""
    values = [0] * arity
    while True:
        yield tuple(values)
        for index in range(arity - 1, -1, -1):
            values[index] += 1
            if values[index] < modulus:
                break
            values[index] = 0
        else:
            return

def verify_certificate(source, certificate, deadline=None):
    if set(certificate) != {'version', 'kind', 'input_sha256', 'modulus'}:
        raise ValueError('invalid certificate fields')
    if type(certificate['version']) is not int or certificate['version'] != 1 or certificate['kind'] != 'integer-residue-exhaustion':
        raise ValueError('invalid certificate kind')
    if certificate['input_sha256'] != hashlib.sha256(source.encode()).hexdigest():
        raise ValueError('input digest mismatch')
    modulus = certificate['modulus']
    if type(modulus) is not int or modulus < 2:
        raise ValueError('invalid modulus')
    if deadline is None:
        deadline = time.monotonic() + 60
    (variables, roots) = problem(source)
    count = 0
    for residue in residue_tuples(modulus, len(variables)):
        if time.monotonic() >= deadline:
            raise TimeoutError('incomplete residue enumeration')
        env = {symbol: integer(value) for (symbol, value) in zip(variables, residue)}
        values = [truth(evaluate(root, env, modulus)) for root in roots]
        count += 1
        if False not in values:
            return dict(status='not_verified', valuations=count)
    return dict(status='verified', modulus=modulus, valuations=count, variables=len(variables), assertions=len(roots))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=60)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error('positive verification timeout required')
    deadline = time.monotonic() + args.timeout
    try:
        source = args.input.read_bytes().decode('utf-8')
        certificate = json.loads(args.certificate.read_text())
        result = verify_certificate(source, certificate, deadline)
    except (Unsupported, ValueError, TimeoutError, RecursionError, IndexError, TypeError) as error:
        print(json.dumps(dict(status='not_verified', reason=str(error))))
        return 2
    print(json.dumps(result))
    return int(result['status'] != 'verified')
if __name__ == '__main__':
    raise SystemExit(main())
