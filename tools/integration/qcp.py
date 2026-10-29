#!/usr/bin/env python3
"""Typed pure-condition bridge for QCP's generated Rocq goals.

This is a conservative source adapter, not a Rocq elaborator or a QCP callback.
Only explicit Z/bool binders and the documented operators below are accepted.
Owned signed-Int cells supply their declared range only in the supported positive
conjunctive assertion grammar. Projections are sufficient subconditions, not
proofs or counterexamples of entire C programs.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re


class Unsupported(ValueError):
    pass


@dataclass(frozen=True)
class Term:
    smt: str
    sort: str
    op: str = ''
    args: tuple[Term, ...] = ()


LIMITS = {
    "INT_MIN": -(1 << 31), "INT_MAX": (1 << 31) - 1,
    "UINT_MAX": (1 << 32) - 1,
    "INT64_MIN": -(1 << 63), "INT64_MAX": (1 << 63) - 1,
    "UINT64_MAX": (1 << 64) - 1,
}
TOKEN = re.compile(r"\s*(<->|->|/\\|\\/|<=|>=|<>|[(),:+*%/^÷=<>~\-]|[0-9]+|[A-Za-z_][A-Za-z_0-9'.]*)")


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"(- {-value})"


def apply(op: str, *args: Term, sort: str) -> Term:
    return Term(f"({op} {' '.join(t.smt for t in args)})", sort, op, args)


def absolute(a: Term) -> Term:
    return apply('ite', apply('<', a, Term('0', 'Int'), sort='Prop'),
                 apply('-', a, sort='Int'), a, sort='Int')


def gcd(a: Term, b: Term) -> Term:
    # Z.gcd is symmetric for all signed integers, including zero. Canonical
    # argument order shares the UF application without introducing quantifiers.
    a, b = sorted((a, b), key=lambda t: t.smt)
    return apply('|qcp.gcd|', a, b, sort='Int')


def integer_function_facts(terms: list[Term]) -> tuple[list[str], list[dict]]:
    """Finite, valid ground instances; SAT remains an inconclusive projection.

    No bounded approximation of gcd and no unrolling to a guessed answer. The
    omitted gcd axioms weaken the query, so UNSAT still suffices. Rocq checks
    the complete source statement independently of these SMT facts.
    """
    applications, remainders = {}, {}
    pending = list(terms)
    visited = set()
    while pending:
        term = pending.pop()
        if term.smt in visited:
            continue
        visited.add(term.smt)
        pending.extend(term.args)
        if term.op == '|qcp.gcd|':
            applications[term.smt] = term
        elif term.op == 'Z.rem':
            remainders[term.smt] = term
    if not applications:
        return [], []
    facts = []
    for remainder in remainders.values():
        a, b = remainder.args
        before, after = gcd(a, b), gcd(b, remainder)
        applications[before.smt] = before
        applications[after.smt] = after
        facts.append(dict(lemma='Z.gcd_rem + Z.gcd_comm',
            assertion=f'(=> (not (= {b.smt} 0)) (= {before.smt} {after.smt}))'))
    for term in applications.values():
        a, b = term.args
        facts.extend([
            dict(lemma='Z.gcd_nonneg', assertion=f'(>= {term.smt} 0)'),
            dict(lemma='Z.gcd_0_l', assertion=f'(=> (= {a.smt} 0) (= {term.smt} {absolute(b).smt}))'),
            dict(lemma='Z.gcd_0_r', assertion=f'(=> (= {b.smt} 0) (= {term.smt} {absolute(a).smt}))'),
        ])
    return ['(declare-fun |qcp.gcd| (Int Int) Int)'], facts


def neg(a: Term) -> Term:
    return apply("not", a, sort="Prop")


def quot(a: Term, b: Term) -> Term:
    """Total Rocq Z.quot: truncation toward zero; division by zero is zero."""
    x, y = a.smt, b.smt
    ax, ay = f"(ite (< {x} 0) (- {x}) {x})", f"(ite (< {y} 0) (- {y}) {y})"
    magnitude = f"(div {ax} {ay})"
    return Term(f"(ite (= {y} 0) 0 (ite (xor (< {x} 0) (< {y} 0)) (- {magnitude}) {magnitude}))", "Int", 'Z.quot', (a, b))


def floor_div(a: Term, b: Term) -> Term:
    # Rocq Z.div rounds toward -infinity even for a negative divisor.
    x, y = a.smt, b.smt
    return Term(f"(ite (= {y} 0) 0 (ite (> {y} 0) (div {x} {y}) (div (- {x}) (- {y}))))", "Int", 'Z.div', (a, b))


def rem(a: Term, b: Term) -> Term:
    """Total Rocq Z.rem, using a sign-preserving remainder normal form."""
    x, y = a.smt, b.smt
    magnitude = f"(mod (ite (< {x} 0) (- {x}) {x}) {y})"
    return Term(f"(ite (= {y} 0) {x} (ite (< {x} 0) (- {magnitude}) {magnitude}))", "Int", 'Z.rem', (a, b))


class Parser:
    precedence = {"<->": 1, "->": 2, "\\/": 3, "/\\": 4,
                  "=": 5, "<>": 5, "<": 5, "<=": 5, ">": 5, ">=": 5,
                  "+": 6, "-": 6, "*": 7, "%": 7, "/": 7, "÷": 7, "^": 8}

    def __init__(self, text: str, symbols: dict[str, str]):
        self.tokens = []
        self.symbols = symbols
        self.index = 0
        self.depth = 0
        self.work = 0
        position = 0
        while position < len(text):
            match = TOKEN.match(text, position)
            if not match:
                if not text[position:].strip():
                    break
                raise Unsupported(f"unrecognized Rocq token near {text[position:position+35]!r}")
            self.tokens.append(match[1])
            position = match.end()
        if len(self.tokens) > 20000:
            raise Unsupported("expression token budget exhausted")

    def peek(self) -> str:
        return self.tokens[self.index] if self.index < len(self.tokens) else ""

    def pop(self, expected: str | None = None) -> str:
        found = self.peek()
        if not found or expected is not None and found != expected:
            raise Unsupported(f"expected {expected or 'term'}, found {found or 'end'}")
        self.index += 1
        return found

    @staticmethod
    def typed(term: Term, sort: str) -> Term:
        if term.sort != sort:
            raise Unsupported(f"expected {sort}, found {term.sort}")
        return term

    def atom(self) -> Term:
        token = self.pop()
        if token == "(":
            result = self.expression()
            self.pop(")")
            return result
        if token in ("-", "~", "not"):
            sort = "Int" if token == "-" else "Prop"
            # Rocq logical negation extends over the following relation.
            a = self.typed(self.expression(8 if token == "-" else 5), sort)
            return apply("-" if token == "-" else "not", a, sort=sort)
        if token.isdecimal():
            return Term(token, "Int")
        if token in LIMITS:
            return Term(integer(LIMITS[token]), "Int")
        if token in ("True", "False", "true", "false"):
            return Term(token.lower(), "Prop" if token[0].isupper() else "Bool")
        if token in ("Zabs", "Z.abs", "Z.opp", "Z.quot", "Z.rem", "Z.div", "Z.modulo", "Zgcd", "Z.gcd"):
            a = self.typed(self.atom(), "Int")
            if token in ("Zabs", "Z.abs"):
                return absolute(a)
            if token == "Z.opp":
                return apply("-", a, sort="Int")
            b = self.typed(self.atom(), "Int")
            if token in ('Zgcd', 'Z.gcd'):
                return gcd(a, b)
            q = quot(a, b) if token in ("Z.quot", "Z.rem") else floor_div(a, b)
            if token == "Z.rem":
                return rem(a, b)
            return apply("-", a, apply("*", b, q, sort="Int"), sort="Int") if token == "Z.modulo" else q
        if token in self.symbols:
            return Term("|" + token + "|", self.symbols[token])
        raise Unsupported(f"undeclared or unsupported symbol {token}")

    def binary(self, op: str, a: Term, b: Term) -> Term:
        if op in ("/\\", "\\/", "->", "<->"):
            self.typed(a, "Prop"); self.typed(b, "Prop")
            return apply({"/\\": "and", "\\/": "or", "->": "=>", "<->": "="}[op], a, b, sort="Prop")
        if op in ("=", "<>"):
            if a.sort != b.sort:
                raise Unsupported("equality sort mismatch")
            if a.sort == "Prop":
                raise Unsupported("Rocq proposition equality is not Boolean equivalence")
            result = apply("=", a, b, sort="Prop")
            return neg(result) if op == "<>" else result
        self.typed(a, "Int"); self.typed(b, "Int")
        if op in ("<", "<=", ">", ">="):
            return apply(op, a, b, sort="Prop")
        if op in ("÷", "%", "/"):
            q = floor_div(a, b) if op == "/" else quot(a, b)
            return rem(a, b) if op == "%" else q
        if op == "^":
            if not b.smt.isdecimal() or int(b.smt) > 256:
                raise Unsupported("power requires a bounded nonnegative literal exponent")
            n = int(b.smt)
            result = Term("1", "Int")
            while n:
                if n & 1:
                    result = apply("*", result, a, sort="Int")
                n >>= 1
                if n:
                    a = apply("*", a, a, sort="Int")
            return result
        return apply(op, a, b, sort="Int")

    def expression(self, minimum: int = 0) -> Term:
        self.depth += 1
        self.work += 1
        if self.depth > 150 or self.work > 20000:
            raise Unsupported("expression construction budget exhausted")
        try:
            left = self.atom()
            while self.peek() in self.precedence and self.precedence[self.peek()] >= minimum:
                op = self.pop()
                level = self.precedence[op]
                right = self.expression(level if op in ("->", "^", "<->") else level + 1)
                # Rocq's chained integer comparisons abbreviate conjunctions.
                if op in ("<", "<=", ">", ">=") and left.sort == "Prop":
                    raise Unsupported("chained comparison requires explicit conjunction")
                left = self.binary(op, left, right)
            return left
        finally:
            self.depth -= 1

    def parse(self) -> Term:
        term = self.expression()
        if self.peek():
            raise Unsupported(f"unconsumed token {self.peek()}")
        return term


def parse(text: str, symbols: dict[str, str]) -> Term:
    return Parser(text, symbols).parse()


def comments(text: str) -> str:
    """Remove nested comments without moving source offsets or line numbers."""
    result = list(text)
    depth = i = 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == "(*":
            depth += 1
            result[i:i+2] = "  "
            i += 2
        elif pair == "*)" and depth:
            depth -= 1
            result[i:i+2] = "  "
            i += 2
        else:
            if depth and text[i] != "\n":
                result[i] = " "
            i += 1
    if depth:
        raise Unsupported("unterminated Rocq comment")
    return "".join(result)


def binders(body: str) -> tuple[dict[str, str], list[Term], str]:
    body = body.strip()
    if not body.startswith("forall "):
        raise Unsupported("goal must start with explicit forall binders")
    position = len("forall ")
    symbols: dict[str, str] = {}
    assumptions = []
    names = set()
    while True:
        while position < len(body) and body[position].isspace():
            position += 1
        if position < len(body) and body[position] == ",":
            return symbols, assumptions, body[position+1:].strip()
        if position >= len(body) or body[position] != "(":
            raise Unsupported("only parenthesized, typed binders are accepted")
        begin, depth = position + 1, 1
        position += 1
        while position < len(body) and depth:
            depth += (body[position] == "(") - (body[position] == ")")
            position += 1
        if depth:
            raise Unsupported("unterminated binder")
        declaration = body[begin:position-1]
        if ":" not in declaration:
            raise Unsupported("binder has no explicit type")
        name, typ = (x.strip() for x in declaration.split(":", 1))
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*", name) or name in names:
            raise Unsupported("invalid or shadowed binder")
        if name in LIMITS or name in {"True", "False", "true", "false", "Zabs", "Zgcd", "not"}:
            raise Unsupported("binder shadows a source-profile intrinsic")
        names.add(name)
        if typ in ("Z", "bool"):
            symbols[name] = "Int" if typ == "Z" else "Bool"
        else:
            assumption = parse(typ, symbols)
            if assumption.sort != "Prop":
                raise Unsupported("unsupported binder type")
            assumptions.append(assumption)


DEFINITION = re.compile(r"\bDefinition\s+([A-Za-z_][A-Za-z_0-9']*)\s*:=")
END = re.compile(r"\.(?=\s*(?:Definition\b|Module\b|End\b|$))")


def assertion_parts(text: str) -> list[str]:
    """Split positive conjunctions, respecting parentheses and both quote kinds.

    Each resulting leaf must still match the complete supported grammar. An
    unknown connective/binder invalidates extraction from the entire assertion.
    """
    result, start, depth, quote, i = [], 0, 0, '', 0
    while i < len(text):
        token = text[i]
        if quote:
            if token == quote:
                quote = ''
        elif token in ('"', '“'):
            quote = '”' if token == '“' else '"'
        elif token == '(':
            depth += 1
        elif token == ')':
            depth -= 1
            if depth < 0:
                raise Unsupported('unbalanced assertion')
        elif depth == 0 and text[i:i+2] in ('**', '&&'):
            result.append(text[start:i].strip())
            i += 2
            start = i
            continue
        i += 1
    if depth or quote:
        raise Unsupported('unterminated assertion')
    result.append(text[start:].strip())
    return result


def assertion_unwrap(text: str) -> str:
    text = text.strip()
    while text.startswith('('):
        depth, quote, end = 0, '', None
        for i, token in enumerate(text):
            if quote:
                if token == quote:
                    quote = ''
            elif token in ('"', '“'):
                quote = '”' if token == '“' else '"'
            elif token == '(':
                depth += 1
            elif token == ')':
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end != len(text) - 1:
            break
        text = text[1:-1].strip()
    return text


def owned_int_ranges(assertion: str, symbols: dict[str, str]) -> list[dict]:
    """Conservative consequences of QCP store_int_range (signed 32-bit Int).

    Fully recognize the positive assertion tree before returning any facts.
    In particular, never mine cells out of disjunctions, negations, wands,
    existential assertions, function applications or unknown heap predicates.
    """
    def visit(text: str, depth: int = 0) -> list[dict]:
        if depth > 100:
            raise Unsupported('assertion nesting budget exhausted')
        text = assertion_unwrap(text)
        parts = assertion_parts(text)
        if len(parts) > 1:
            return [fact for part in parts for fact in visit(part, depth + 1)]
        if text in ('TT', 'emp'):
            return []
        if text.startswith('“') and text.endswith('”') and text.count('“') == 1:
            if parse(text[1:-1], symbols).sort != 'Prop':
                raise Unsupported('non-propositional assertion')
            return []
        cell = re.fullmatch(r'(.+?)\s*#\s*Int\s*\|->\s*(.+)', text, re.DOTALL)
        if not cell:
            raise Unsupported('unsupported positive assertion leaf')
        address, value = assertion_unwrap(cell[1]), assertion_unwrap(cell[2])
        # Addresses are retained for checked proof reconstruction, never asserted
        # as arithmetic facts. Recognize a variable address or a typed Z term.
        if not re.fullmatch(r'&\(\s*"[A-Za-z_][A-Za-z_0-9]*"\s*\)', address):
            if parse(address, symbols).sort != 'Int':
                raise Unsupported('unsupported cell address')
        term = parse(value, symbols)
        if term.sort != 'Int':
            raise Unsupported('non-integer cell value')
        lower = apply('<=', Term(integer(LIMITS['INT_MIN']), 'Int'), term, sort='Prop')
        upper = apply('<=', term, Term(integer(LIMITS['INT_MAX']), 'Int'), sort='Prop')
        return [dict(kind='owned-int-range', address=address, value=value,
                     lemma='store_int_range', lower=lower.smt, upper=upper.smt)]

    try:
        return visit(assertion)
    except (Unsupported, RecursionError):
        # Retain the previous weaker pure projection; unsupported heap syntax
        # cannot cause a stronger arithmetic assumption to escape.
        return []


def sufficient_leaves(body: str, definitions: dict[str, str], stack=()) -> list[dict]:
    """Expand a sufficient proof tree without treating whole VCs as axioms.

    Proving the left disjunct proves a disjunction; proving the consequent
    proves an implication. These intentionally stronger obligations can fail
    even when the source VC is valid. Conjunctions require both children.
    """
    if len(stack) > 100:
        raise Unsupported('definition expansion budget exhausted')
    body = assertion_unwrap(body)
    if body.startswith('forall '):
        return [dict(body=body, proof_path=[])]
    if body in definitions:
        if body in stack:
            raise Unsupported('cyclic goal definition')
        leaves = sufficient_leaves(definitions[body], definitions, (*stack, body))
        return [{**leaf, 'proof_path': [dict(unfold=body), *leaf['proof_path']]} for leaf in leaves]
    depth, quote, i, operators = 0, '', 0, []
    while i < len(body):
        char = body[i]
        if quote:
            if char == quote:
                quote = ''
        elif char in ('"', '“'):
            quote = '”' if char == '“' else '"'
        elif char == '(':
            depth += 1
        elif char == ')':
            depth -= 1
            if depth < 0:
                raise Unsupported('unbalanced goal composition')
        elif depth == 0 and body[i:i+2] in ('\\/', '/\\', '->'):
            operators.append((body[i:i+2], i))
            i += 1
        i += 1
    if depth or quote:
        raise Unsupported('unterminated goal composition')
    if operators:
        # Rocq connects conjunction more tightly than disjunction, and both
        # more tightly than implication. All three associate to the right.
        op, i = min(operators, key=lambda item: ({'->': 0, '\\/': 1, '/\\': 2}[item[0]], item[1]))
        left, right = body[:i], body[i+2:]
        children = ([('left', left)] if op == '\\/' else
                    [('consequent', right)] if op == '->' else
                    [('conj-left', left), ('conj-right', right)])
        result = []
        for direction, child in children:
            result.extend({**leaf, 'proof_path': [dict(direction=direction), *leaf['proof_path']]}
                          for leaf in sufficient_leaves(child, definitions, (*stack, op)))
        return result
    raise Unsupported('expected a typed goal or supported goal composition')


def export_goals(source: Path, output: Path) -> dict:
    raw_bytes = source.read_bytes()
    raw = raw_bytes.decode('utf-8')
    text = comments(raw)
    digest = hashlib.sha256(raw_bytes).hexdigest()
    output.mkdir(parents=True, exist_ok=True)
    report: dict = {"source": str(source), "source_sha256": digest, "goals": [], "queries": [],
                    "semantics": "Rocq Z/bool; % is Z.rem; division by zero follows Rocq total functions",
                    "program_verified": False}
    definitions = {}
    for match in DEFINITION.finditer(text):
        end = END.search(text, match.end())
        if end:
            definitions[match[1]] = text[match.end():end.start()]
    for match in DEFINITION.finditer(text):
        end = END.search(text, match.end())
        record = {"name": match[1], "line": text.count("\n", 0, match.start()) + 1}
        report["goals"].append(record)
        try:
            if not end:
                raise Unsupported("definition terminator not found")
            leaves = sufficient_leaves(text[match.end():end.start()], definitions, (match[1],))
            built = []
            for leaf_index, leaf in enumerate(leaves):
                conditions, details = export_leaf(leaf['body'])
                if len(leaves) == 1:
                    record.update(details)
                    record['proof_path'] = leaf['proof_path']
                for script, expression, facts in conditions:
                    i = len(built)
                    filename = f"{match[1]}-{i}.smt2"
                    built.append((filename, script, expression,
                                  dict(**details, proof_path=leaf['proof_path'], leaf=leaf_index,
                                       integer_function_facts=facts)))
            for filename, script, expression, details in built:
                (output / filename).write_bytes(script.encode('utf-8'))
                report["queries"].append({**record, **details, "file": filename,
                                          "conclusion": expression,
                                          "query_sha256": hashlib.sha256(script.encode()).hexdigest()})
            record["status"] = "exported"
            record["query_count"] = len(built)
        except (Unsupported, RecursionError) as exc:
            record["status"] = "unsupported"
            record["reason"] = str(exc)
    (output / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def export_leaf(body: str) -> tuple[list[tuple[str, str, list[dict]]], dict]:
    symbols, assumptions, body = binders(body)
    projection = "pure"
    conclusions = []
    if "|--" in body:
        if body.count("|--") != 1:
            raise Unsupported("compound entailment requires an elaborated AST")
        lhs, rhs = body.split("|--")
        ranges = owned_int_ranges(lhs, symbols)
        for fact in ranges:
            # Preserve function dependencies in values derived from heap cells.
            value = parse(fact['value'], symbols)
            assumptions.extend(Term(fact[key], 'Prop', 'owned-bound', (value,))
                               for key in ('lower', 'upper'))
        projection = "pure-sufficient-condition"
        rest = rhs.strip()
        while rest.startswith("“"):
            last = rest.find("”")
            if last < 0:
                raise Unsupported("unterminated pure assertion")
            conclusions.append(rest[1:last])
            rest = rest[last+1:].strip()
            if not rest.startswith("&&"):
                break
            rest = rest[2:].strip()
        if not conclusions:
            raise Unsupported("no leading pure RHS assertion")
        residual_heap = bool(rest)
    else:
        conclusions = [body]
    built = []
    for expression in conclusions:
        term = parse(expression, symbols)
        if term.sort != "Prop":
            raise Unsupported("conclusion must be a proposition")
        script = ["(set-logic ALL)"]
        declarations, facts = integer_function_facts([*assumptions, term])
        script += declarations
        script += [f"(declare-const |{name}| {sort})" for name, sort in symbols.items()]
        script += [f"(assert {f['assertion']})" for f in facts]
        script += [f"(assert {a.smt})" for a in assumptions]
        script += [f"(assert (not {term.smt}))", "(check-sat)", "(exit)", ""]
        built.append(("\n".join(script), expression, facts))
    details = dict(kind=projection)
    if projection != 'pure':
        details.update(derived_assumptions=ranges, residual_heap=residual_heap)
    return built, details


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source", type=Path)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    r = export_goals(args.source, args.output)
    print(json.dumps({"goals": len(r["goals"]), "queries": len(r["queries"]),
                      "unsupported": sum(g["status"] == "unsupported" for g in r["goals"])}))


if __name__ == "__main__":
    main()
