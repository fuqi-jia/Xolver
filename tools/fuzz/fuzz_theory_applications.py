#!/usr/bin/env python3
"""Differential native-theory queries and independent replay of exported models."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys

from fuzz_quantifiers import invoke

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'proof'))
from isabelle_pa import Atom, parse


def emit(node):
    # Benchmark assertions and exported models can exceed Python's recursion
    # limit. Keep the shared replay serializer iterative, including nested lets.
    pieces, pending = [], [(True, node)]
    while pending:
        is_node, item = pending.pop()
        if not is_node:
            pieces.append(item)  # punctuation inserted below
        elif isinstance(item, list):
            pieces.append('(')
            pending.append((False, ')'))
            for index in range(len(item) - 1, -1, -1):
                pending.append((True, item[index]))
                if index:
                    pending.append((False, ' '))
        elif isinstance(item, Atom):
            if item.kind == 'string':
                pieces.append('"' + item.text.replace('"', '""') + '"')
            else:
                pieces.append('|' + item.text + '|' if item.kind == 'quoted' else item.text)
        else:
            raise ValueError('invalid model syntax')
    return ''.join(pieces)


def model_symbols(node, bound=()):
    """Collect free term symbols without confusing binders or numeral literals."""
    names, pending = set(), [(node, frozenset(bound))]
    simple = re.compile(r'[a-zA-Z~!@$%^&*_\-+=<>.?/][a-zA-Z0-9~!@$%^&*_\-+=<>.?/]*\Z')
    while pending:
        item, scope = pending.pop()
        if isinstance(item, Atom):
            if (item.kind == 'quoted' or (item.kind == 'symbol' and
                    simple.fullmatch(item.text) and item.text not in ('true', 'false'))):
                if item.text not in scope:
                    names.add(item.text)
            continue
        if not isinstance(item, list) or not item:
            continue
        op = item[0].text if isinstance(item[0], Atom) and item[0].kind == 'symbol' else None
        if op in ('forall', 'exists', 'lambda', 'let'):
            if len(item) != 3 or not isinstance(item[1], list):
                raise ValueError('malformed model binder')
            local = set()
            for binding in item[1]:
                if (not isinstance(binding, list) or len(binding) != 2 or
                        not isinstance(binding[0], Atom) or binding[0].kind == 'string'):
                    raise ValueError('malformed model binder')
                local.add(binding[0].text)
                if op == 'let':
                    pending.append((binding[1], scope))  # SMT-LIB lets are parallel.
            pending.append((item[2], scope | local))
        elif op in ('!', 'as') and len(item) >= 2:
            pending.append((item[1], scope))
        elif op != '_':
            pending.extend((child, scope) for child in item)
    return names


def model_universes(original_commands, definitions, auxiliary, constraints):
    """Encode each supplied opaque domain as an exact finite enumeration."""
    sorts, aliases, terms = {}, {}, set()
    for command in original_commands:
        op = emit(command[0])
        if op == 'declare-sort' and len(command) == 3 and emit(command[2]) == '0':
            sorts[command[1].text] = command[1]
        elif op == 'define-sort' and len(command) == 4 and command[2] == []:
            aliases[command[1].text] = command[3]
        elif op in ('declare-const', 'declare-fun', 'define-fun'):
            terms.add(command[1].text)

    def root_sort(sort):
        seen = set()
        while isinstance(sort, Atom) and sort.kind != 'string':
            if sort.text in sorts:
                return sort.text
            if sort.text in seen:
                raise ValueError('cyclic model sort alias')
            seen.add(sort.text)
            if sort.text not in aliases:
                break
            sort = aliases[sort.text]
        return None

    def sort_key(sort):
        root = root_sort(sort)
        return ('declared', root) if root else ('other',
            sort.text if isinstance(sort, Atom) else emit(sort))

    uses, active = {}, set()
    for name in terms & definitions.keys():
        definition = definitions[name]
        if not isinstance(definition[2], list):
            raise ValueError('malformed model function parameters')
        parameters = []
        for parameter in definition[2]:
            if (not isinstance(parameter, list) or len(parameter) != 2 or
                    not isinstance(parameter[0], Atom)):
                raise ValueError('malformed model function parameters')
            parameters.append(parameter[0].text)
        used = model_symbols(definition[4], parameters) & auxiliary.keys()
        roots = set()
        for value in used:
            declaration = auxiliary[value]
            root = root_sort(declaration[3])
            if declaration[2] or root is None:
                raise ValueError('unsupported auxiliary model domain')
            roots.add(root)
        uses[name] = roots
        active.update(roots)

    members, by_sort = {}, {}
    for name, declaration in auxiliary.items():
        by_sort.setdefault(sort_key(declaration[3]), set()).add(name)
        root = root_sort(declaration[3])
        if root in active:
            if declaration[2]:
                raise ValueError('unsupported auxiliary model domain')
            members.setdefault(root, []).append(declaration[1])

    provided = {}
    for constraint in constraints:
        binders = constraint[1]
        if (len(binders) != 1 or not isinstance(binders[0], list) or
                len(binders[0]) != 2 or not isinstance(binders[0][0], Atom)):
            raise ValueError('unsupported model universe constraint')
        variable, sort = binders[0]
        body = constraint[2]
        if model_symbols(body, {variable.text}) & terms:
            raise ValueError('model universe constraint references original symbol')
        choices = body[1:] if isinstance(body, list) and body and emit(body[0]) == 'or' else [body]
        values = set()
        for choice in choices:
            if not isinstance(choice, list) or len(choice) != 3 or emit(choice[0]) != '=':
                raise ValueError('unsupported model universe constraint')
            left, right = choice[1:]
            if not isinstance(left, Atom) or not isinstance(right, Atom):
                raise ValueError('unsupported model universe constraint')
            if left.text == variable.text and model_symbols(left) == {variable.text}:
                value = right
            elif right.text == variable.text and model_symbols(right) == {variable.text}:
                value = left
            else:
                raise ValueError('unsupported model universe constraint')
            if value.text == variable.text or model_symbols(value) != {value.text}:
                raise ValueError('unsupported model universe constraint')
            values.add(value.text)
        if not values or values != by_sort.get(sort_key(sort)):
            raise ValueError('incomplete model universe enumeration')
        root = root_sort(sort)
        if root in active:
            # Expand a sort alias without changing its carrier or membership.
            normalized = [constraint[0], [[variable, sorts[root]]], constraint[2]]
            provided.setdefault(root, []).append('(assert ' + emit(normalized) + ')')

    preludes, domains = {}, {}
    for root, values in members.items():
        # Nullary constructors enforce both distinctness and exhaustiveness.
        # This is the same finite carrier as domain-closure axioms, without
        # asking a checker to discover a model for a new universal formula.
        domains[root] = emit([Atom('declare-datatype'), sorts[root], [[value] for value in values]])
        preludes[root] = provided.get(root, [])
    return preludes, uses, domains


def replay(prefix, output):
    def symbol_name(node):
        if not isinstance(node, Atom) or node.kind == 'string':
            raise ValueError('expected model symbol')
        # |x| and x denote the same SMT-LIB symbol. Solvers may remove optional
        # quoting when exporting a model; use semantic names for the join.
        return node.text

    expressions = parse(output)
    if len(expressions) != 2 or emit(expressions[0]) != 'sat':
        raise ValueError('expected SAT followed by exactly one model')
    bindings = expressions[1]
    if not isinstance(bindings, list):
        raise ValueError('expected model bindings')
    if bindings and isinstance(bindings[0], Atom) and emit(bindings[0]) == 'model':
        bindings = bindings[1:]
    original_commands = parse(prefix)
    original_symbols = {symbol_name(command[1]) for command in original_commands
                        if emit(command[0]) in ('declare-const', 'declare-fun',
                                                'declare-sort', 'define-fun', 'define-sort')}
    definitions, auxiliary_declarations, universe_constraints = {}, {}, []
    for binding in bindings:
        if not isinstance(binding, list) or not binding:
            raise ValueError('unsupported model binding')
        op = emit(binding[0])
        if op == 'forall' and len(binding) == 3 and isinstance(binding[1], list):
            universe_constraints.append(binding)
            continue
        if not ((op == 'define-fun' and len(binding) == 5)
                or (op == 'declare-fun' and len(binding) == 4
                    and isinstance(binding[2], list))):
            raise ValueError('unsupported model binding')
        name = symbol_name(binding[1])
        if name in definitions or name in auxiliary_declarations:
            raise ValueError('duplicate model definition')
        if op == 'define-fun':
            if (not isinstance(binding[2], list) or any(
                    not isinstance(parameter, list) or len(parameter) != 2 or
                    not isinstance(parameter[0], Atom) or parameter[0].kind == 'string'
                    for parameter in binding[2])):
                raise ValueError('malformed model function parameters')
            if len({parameter[0].text for parameter in binding[2]}) != len(binding[2]):
                raise ValueError('duplicate model function parameter')
            definitions[name] = binding
        else:
            if name in original_symbols:
                raise ValueError('model declaration shadows original symbol ' + name)
            auxiliary_declarations[name] = binding

    universes, universe_uses, domains = model_universes(
        original_commands, definitions, auxiliary_declarations, universe_constraints)
    algebraic_prelude = []
    if 'root-of-with-interval' in output or 'root-obj' in output:
        names = [symbol_name(command[1]) for command in original_commands
                 if emit(command[0]) in ('declare-const', 'declare-fun')]
        from algebraic_model import expand_algebraic_roots
        selected, algebraic_prelude = expand_algebraic_roots(
            [definitions[name] for name in names if name in definitions], original_commands)
        definitions.update({symbol_name(binding[1]): binding for binding in selected})
    commands, inserted_roots = [], False
    inserted_universes, declared_sorts = set(), set()
    extended_models = bool(universes) or any(
        emit(command[0]) == 'define-fun' and symbol_name(command[1]) in definitions
        and definitions[symbol_name(command[1])][2] for command in original_commands)
    reserved = original_symbols | definitions.keys() | auxiliary_declarations.keys()
    for binding in definitions.values():
        reserved.update(model_symbols(binding[4]))
        reserved.update(symbol_name(parameter[0]) for parameter in binding[2])

    def fresh(base):
        while base in reserved:
            base += '_'
        reserved.add(base)
        return Atom(base)

    def insert_universes(name):
        for root in sorted(universe_uses.get(name, set()) - inserted_universes):
            if root not in declared_sorts:
                raise ValueError('model domain used before its sort declaration')
            commands.extend(universes[root])
            inserted_universes.add(root)

    def check_signature(command, binding):
        op = emit(command[0])
        args, result = ([], command[2]) if op == 'declare-const' else (
            [parameter[1] for parameter in command[2]] if op == 'define-fun'
            else command[2], command[3])
        if (emit(result) != emit(binding[3]) or len(args) != len(binding[2])
                or any(emit(a) != emit(b[1]) for a, b in zip(args, binding[2]))):
            raise ValueError('model signature mismatch for ' + symbol_name(command[1]))

    if extended_models and not any(emit(command[0]) == 'set-logic' for command in original_commands):
        commands.append('(set-logic ALL)')
    for command in original_commands:
        op = emit(command[0])
        if extended_models and op == 'set-logic':
            commands.append('(set-logic ALL)')  # Finite carrier types and function checks extend the replay language.
            continue
        if algebraic_prelude and op == 'set-logic':
            # Keep an existing real polynomial logic: widening QF_NRA to ALL
            # can disable the independent checker's specialized arithmetic
            # procedure. Other source logics may need a wider replay language.
            commands.append(emit(command) if len(command) == 2 and
                            emit(command[1]) in ('ALL', 'QF_NRA', 'NRA')
                            else '(set-logic ALL)')
            continue
        if (algebraic_prelude and not inserted_roots
                and op not in ('set-option', 'set-info')):
            commands.extend(algebraic_prelude)
            inserted_roots = True
        if op in ('declare-const', 'declare-fun'):
            name = symbol_name(command[1])
            if name not in definitions:
                raise ValueError('missing interpretation for ' + name)
            insert_universes(name)
            binding = definitions[name]
            check_signature(command, binding)
            commands.append(emit(binding))
        elif op == 'define-fun' and symbol_name(command[1]) in definitions:
            # A source-defined function is already fixed by the query. Check
            # any printed interpretation against it rather than silently
            # ignoring that interpretation or replacing the original definition.
            name = symbol_name(command[1])
            binding = definitions[name]
            check_signature(command, binding)
            commands.append(emit(command))
            insert_universes(name)
            alias = fresh('__xolver_model_function')
            params = [[fresh('__xolver_model_argument'), p[1]] for p in binding[2]]
            body = [command[1], *[p[0] for p in params]] if params else command[1]
            commands.append(emit([Atom('define-fun'), alias, params, binding[3], body]))
            call = [alias, *[p[0] for p in binding[2]]] if binding[2] else alias
            equality = [Atom('='), call, binding[4]]
            if binding[2]:
                equality = [Atom('forall'), binding[2], equality]
            commands.append(emit([Atom('assert'), equality]))
        elif op == 'declare-sort' and symbol_name(command[1]) in domains:
            name = symbol_name(command[1])
            commands.append(domains[name])
            declared_sorts.add(name)
        else:
            commands.append(emit(command))
            if op == 'declare-sort':
                declared_sorts.add(symbol_name(command[1]))
    return '\n'.join(commands) + '\n(check-sat)\n'


def integer(n):
    return str(n) if n >= 0 else f'(- {-n})'


def string(s):
    return '"' + ''.join('""' if c == '"' else c if 32 <= ord(c) <= 126 and c != '\\'
                         else f'\\u{{{ord(c):x}}}' for c in s) + '"'


def fp_value(bits):
    # Five-bit encoding: sign=1, exponent=2, trailing significand=2.
    sign, exponent, fraction = bits >> 4, (bits >> 2) & 3, bits & 3
    if exponent == 3:
        return None if fraction else float('-inf') if sign else float('inf')
    value = fraction / 4 if exponent == 0 else (1 + fraction / 4) * 2 ** (exponent - 1)
    return -value if sign else value


def cases(seed, count):
    rng = random.Random(seed)
    for i in range(count * 2):
        a, b = rng.randrange(32), rng.randrange(32)
        va, vb = fp_value(a), fp_value(b)
        op = ('fp.eq', 'fp.lt', 'fp.leq', 'fp.gt', 'fp.geq', '=')[i % 6]
        expected = (va is None and vb is None or a == b) if op == '=' else (
            va is not None and vb is not None and {
                'fp.eq': lambda: va == vb, 'fp.lt': lambda: va < vb,
                'fp.leq': lambda: va <= vb, 'fp.gt': lambda: va > vb,
                'fp.geq': lambda: va >= vb}[op]())
        prefix = ('(declare-const x (_ FloatingPoint 2 3))'
                  '(declare-const y (_ FloatingPoint 2 3))'
                  f'(assert (= x ((_ to_fp 2 3) (_ bv{a} 5))))'
                  f'(assert (= y ((_ to_fp 2 3) (_ bv{b} 5))))'
                  f'(assert ({op} x y))')
        yield f'fp-order-{i}', prefix, expected
    for bits in range(32):
        sign, exponent, fraction = bits >> 4, (bits >> 2) & 3, bits & 3
        predicates = [('fp.isNaN', exponent == 3 and fraction != 0),
                      ('fp.isInfinite', exponent == 3 and fraction == 0),
                      ('fp.isZero', exponent == 0 and fraction == 0),
                      ('fp.isNormal', exponent not in (0, 3)),
                      ('fp.isSubnormal', exponent == 0 and fraction != 0),
                      ('fp.isNegative', bool(sign) and not (exponent == 3 and fraction != 0)),
                      ('fp.isPositive', not sign and not (exponent == 3 and fraction != 0))]
        expected = predicates[bits % len(predicates)][1]
        op = predicates[bits % len(predicates)][0]
        yield f'fp-class-{bits}', ('(declare-const x (_ FloatingPoint 2 3))'
                                  f'(assert (= x ((_ to_fp 2 3) (_ bv{bits} 5))))'
                                  f'(assert ({op} x))'), expected
    for i in range(count):
        lo = rng.randrange(-8, 8)
        hi = lo + rng.randrange(0, 7)
        prefix = ('(declare-const x Int)(declare-const r Real)'
                  '(assert (= (to_real x) r))'
                  f'(assert (> r (/ {integer(lo)} 2)))'
                  f'(assert (< r (/ {integer(hi)} 2)))')
        expected = any(lo < 2 * x < hi for x in range(-8, 12))
        yield f'mixed-linear-{i}', prefix, expected
    # Every free result is checked by replaying the emitted interpretation in
    # both external solvers; satisfiability alone would not test rounding.
    formats = [(2, 3), (3, 4), (5, 11), (8, 24)]
    rounding = ['RNE', 'RNA', 'RTP', 'RTN', 'RTZ']
    for i in range(count * 5):
        e, precision = formats[i % len(formats)]
        width = e + precision
        a, b = rng.randrange(1 << width), rng.randrange(1 << width)
        operation = ['fp.add', 'fp.sub', 'fp.mul', 'fp.div'][(i // 5) % 4]
        mode = rounding[i % 5]
        ty = f'(_ FloatingPoint {e} {precision})'
        x = f'((_ to_fp {e} {precision}) (_ bv{a} {width}))'
        y = f'((_ to_fp {e} {precision}) (_ bv{b} {width}))'
        prefix = (f'(declare-const x {ty})(declare-const y {ty})(declare-const result {ty})'
                  f'(assert (= x {x}))(assert (= y {y}))'
                  f'(assert (= result ({operation} {mode} x y)))')
        yield f'fp-arithmetic-{i}', prefix, True
    for mode in rounding:
        for operation in ['fp.add', 'fp.sub', 'fp.mul', 'fp.div']:
            for a, b in [(0, 0), (16, 0), (0, 16), (16, 16), (12, 28),
                         (12, 0), (1, 8), (11, 8), (13, 4), (4, 20)]:
                prefix = ('(declare-const result (_ FloatingPoint 2 3))'
                          f'(assert (= result ({operation} {mode}'
                          f' ((_ to_fp 2 3) (_ bv{a} 5)) ((_ to_fp 2 3) (_ bv{b} 5)))))')
                yield f'fp-edge-{operation}-{mode}-{a}-{b}', prefix, True
    yield 'fp-symbolic-rounding', ('(declare-const mode RoundingMode)'
        '(declare-const result (_ FloatingPoint 2 3))'
        '(assert (distinct mode RTZ))'
        '(assert (= result (fp.add mode (fp #b0 #b01 #b00) (fp #b0 #b00 #b01))))'), True
    for i in range(count):
        a, b, c = (rng.randrange(8) for _ in range(3))
        yield f'uf-{i}', ('(declare-fun f ((_ BitVec 3)) (_ BitVec 3))'
                          '(declare-const x (_ BitVec 3))'
                          f'(assert (= x (_ bv{a} 3)))'
                          f'(assert (= (f x) (_ bv{b} 3)))'
                          f'(assert (= (f (_ bv{a} 3)) (_ bv{c} 3)))'), b == c
        index, value = rng.randrange(4), rng.randrange(8)
        yield f'array-{i}', ('(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))'
                             '(declare-const b (Array (_ BitVec 2) (_ BitVec 3)))'
                             f'(assert (= a ((as const (Array (_ BitVec 2) (_ BitVec 3))) (_ bv{b} 3))))'
                             f'(assert (= b (store a (_ bv{index} 2) (_ bv{value} 3))))'
                             f'(assert (= (select b (_ bv{index} 2)) (_ bv{c} 3)))'), value == c
    words = ['', 'a', 'abba', '007', 'a"b', '\\u', '\U0001f600a', '\x00']
    for i in range(count * 2):
        a, b = rng.choice(words), rng.choice(words)
        start, length = rng.randrange(-1, len(a) + 2), rng.randrange(-1, 5)
        operations = [
            (f'(str.len s)', str(len(a))),
            (f'(str.++ s {string(b)})', string(a + b)),
            (f'(str.substr s {integer(start)} {integer(length)})',
             string(a[start:start + length] if start >= 0 and length > 0 else '')),
            (f'(str.indexof s {string(b)} {integer(start)})',
             integer(a.find(b, start) if 0 <= start <= len(a) else -1)),
            (f'(str.contains s {string(b)})', str(b in a).lower()),
            (f'(str.replace s {string(b)} "z")', string(a.replace(b, 'z', 1))),
            (f'(str.replace_all s {string(b)} "z")', string(a.replace(b, 'z') if b else a)),
            ('(str.to_int s)', integer(int(a) if a and all('0' <= c <= '9' for c in a) else -1)),
        ]
        term, value = operations[i % len(operations)]
        relation = '=' if i % 3 else 'distinct'
        yield f'string-{i}', (f'(declare-const s String)(assert (= s {string(a)}))'
                              f'(assert ({relation} {term} {value}))'), relation == '='
    for i, a in enumerate(words):
        yield f'regex-{i}', (f'(declare-const s String)(assert (= s {string(a)}))'
                             '(assert (str.in_re s (re.* (re.union (str.to_re "a")'
                             ' (str.to_re "b")))))'), all(c in 'ab' for c in a)
    yield 'free-fp', ('(declare-const x (_ FloatingPoint 8 24))(declare-const unused RoundingMode)'
                      '(assert (fp.isSubnormal x))'), True
    yield 'free-string', '(declare-const s String)(assert (str.contains s "abc"))', True
    yield 'empty-string', '(declare-const s String)(assert (= (str.len s) 0))', True
    yield 'free-array', ('(declare-const a (Array (_ BitVec 2) (_ BitVec 3)))'
                         '(assert (= (select a #b00) #b101))(assert (= (select a #b11) #b011))'), True
    yield 'free-uf', ('(declare-fun f ((_ BitVec 3)) (_ BitVec 3))'
                      '(assert (= (f #b000) #b101))(assert (= (f #b001) #b011))'), True
    yield 'bool-array', ('(declare-const a (Array Bool Bool))'
                        '(assert (select a true))(assert (not (select a false)))'), True
    yield 'constant-integer-uf', ('(declare-fun f (Int) Int)'
                                 '(assert (= (f 2) 4))'), True
    yield 'constant-integer-uf-conflict', ('(declare-fun f (Int) Int)'
                                          '(assert (= (f 2) 4))(assert (= (f 2) 5))'), False
    yield 'constant-real-uf', ('(declare-fun f (Real) Real)'
                               '(assert (= (f 2.0) (/ 1.0 2.0)))'), True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--count', type=int, default=32)
    parser.add_argument('--seed', type=int, default=20261023)
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--z3', default=shutil.which('z3'))
    parser.add_argument('--cvc5', default=shutil.which('cvc5'))
    args = parser.parse_args()
    if args.count <= 0 or args.timeout <= 0 or not args.z3 or not args.cvc5:
        parser.error('positive count/timeout and both independent oracles are required')
    args.output.mkdir(parents=True, exist_ok=False)
    commands = {'xolver': [str(args.solver.resolve()), 'solve'],
                'z3': [str(Path(args.z3).resolve())],
                'cvc5': [str(Path(args.cvc5).resolve()), '--lang=smt2', '--fp-exp', '--arrays-exp']}
    versions = {}
    for name, command in commands.items():
        if name == 'xolver':
            continue
        version = subprocess.run([command[0], '--version'], capture_output=True, text=True, timeout=10)
        versions[name] = dict(version=version.stdout.splitlines()[0] if version.stdout else version.stderr[:200],
                              sha256=hashlib.sha256(Path(command[0]).read_bytes()).hexdigest())
    failures, total, models = [], 0, 0
    for name, body, expected_bool in cases(args.seed, args.count):
        expected = 'sat' if expected_bool else 'unsat'
        prefix = '(set-logic ALL)\n(set-option :produce-models true)\n' + body + '\n'
        source = args.output / (name + '.smt2')
        source.write_text(prefix + '(check-sat)\n')
        results = {engine: invoke(command, source, args.timeout,
                                  ('--verbose',) if engine == 'xolver' else ())
                   for engine, command in commands.items()}
        row = dict(case=name, expected=expected, sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   engines=results)
        total += 1
        for engine, result in results.items():
            if result['verdict'] != expected:
                failures.append(dict(case=name, engine=engine, expected=expected, actual=result['verdict']))
        if results['xolver']['verdict'] == 'unknown':
            diagnostic = subprocess.run(commands['xolver'] + [str(source), '--features'],
                                        capture_output=True, text=True, timeout=args.timeout)
            row['features'] = dict(stdout=diagnostic.stdout, stderr=diagnostic.stderr,
                                   returncode=diagnostic.returncode)
        if results['xolver']['verdict'] == 'sat':
            query = args.output / (name + '-model.smt2')
            query.write_text(prefix + '(check-sat)(get-model)\n')
            candidate = invoke(commands['xolver'], query, args.timeout, ('--verbose',))
            row['model'] = candidate
            try:
                if candidate['verdict'] != 'sat':
                    raise ValueError('model query failed')
                pinned = args.output / (name + '-replay.smt2')
                pinned.write_text(replay(prefix, candidate['stdout']))
                checked = {engine: invoke(command, pinned, args.timeout)
                           for engine, command in commands.items() if engine != 'xolver'}
                row['replay'] = checked
                for engine, result in checked.items():
                    if result['verdict'] != 'sat':
                        failures.append(dict(case=name, engine=engine, model=result['verdict']))
                models += 1
            except ValueError as error:
                row['model_error'] = str(error)
                failures.append(dict(case=name, model_error=str(error)))
        with (args.output / 'cases.jsonl').open('a') as stream:
            stream.write(json.dumps(row) + '\n')
    summary = dict(cases=total, models=models, failures=failures, commands=commands, oracles=versions, seed=args.seed,
                   solver_sha256=hashlib.sha256(args.solver.read_bytes()).hexdigest())
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))
    return int(bool(failures) or not models)


if __name__ == '__main__':
    raise SystemExit(main())
