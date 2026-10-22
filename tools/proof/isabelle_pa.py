#!/usr/bin/env python3
"""Translate one original SMT-LIB PA query to an independently replayable theorem.

This translator is part of the trust boundary. Isabelle checks the HOL theorem,
not this translation or the C++ solver. Generation alone is not verification.
No input text is interpolated into Isabelle identifiers, comments or ML.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import re

import pa_trace


class Unsupported(ValueError):
    pass


@dataclass(frozen=True)
class Atom:
    text: str
    kind: str = "symbol"


def parse(source: str) -> list:
    """Read S-expressions, preserving quoted symbols and string boundaries."""
    root, stack = [], []
    target = root
    i = 0
    while i < len(source):
        ch = source[i]
        if ch.isspace():
            i += 1
        elif ch == ";":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end + 1
        elif ch == "(":
            child = []
            target.append(child)
            stack.append(target)
            target = child
            i += 1
        elif ch == ")":
            if not stack:
                raise Unsupported("unmatched closing parenthesis")
            target = stack.pop()
            i += 1
        elif ch in '|\"':
            quote, start, pieces = ch, i, []
            i += 1
            while i < len(source):
                if source[i] == quote:
                    if quote == '"' and i + 1 < len(source) and source[i + 1] == '"':
                        pieces.append('"')
                        i += 2
                        continue
                    break
                if quote == "|" and source[i] == "\\":
                    raise Unsupported("backslash in quoted symbol")
                pieces.append(source[i])
                i += 1
            if i == len(source):
                raise Unsupported(f"unterminated token at {start}")
            target.append(Atom("".join(pieces), "quoted" if quote == "|" else "string"))
            i += 1
        else:
            end = i + 1
            while end < len(source) and not source[end].isspace() and source[end] not in '();|"':
                end += 1
            target.append(Atom(source[i:end]))
            i = end
    if stack:
        raise Unsupported("unclosed parenthesis")
    return root


def keyword(node) -> str:
    if not isinstance(node, Atom) or node.kind != "symbol":
        raise Unsupported("expected unquoted operator")
    return node.text


def symbol(node) -> str:
    if not isinstance(node, Atom) or node.kind == "string":
        raise Unsupported("expected symbol")
    if not node.text or (node.kind == "symbol" and not re.fullmatch(
            r"[a-zA-Z~!@$%^&*_\-+=<>.?/][a-zA-Z0-9~!@$%^&*_\-+=<>.?/]*", node.text)):
        raise Unsupported("invalid symbol")
    if node.kind == "symbol" and node.text in {"true", "false", "let", "forall", "exists", "_", "!"}:
        raise Unsupported("reserved symbol")
    return node.text


def sort(node) -> str:
    result = keyword(node)
    if result not in {"Int", "Bool"}:
        raise Unsupported("only Int and Bool sorts are supported")
    return result


@dataclass(frozen=True)
class Linear:
    constant: int = 0
    coefficients: tuple[tuple[str, int], ...] = ()

    def add(self, other: Linear) -> Linear:
        coefficients = dict(self.coefficients)
        for name, value in other.coefficients:
            coefficients[name] = coefficients.get(name, 0) + value
        return Linear(self.constant + other.constant,
                      tuple(sorted((n, v) for n, v in coefficients.items() if v)))

    def scale(self, factor: int) -> Linear:
        return Linear(self.constant * factor,
                      tuple((n, v * factor) for n, v in self.coefficients if v * factor))

    def hol(self) -> str:
        values = [f"({integer(c).hol} * ({n} :: int))" for n, c in self.coefficients]
        if self.constant or not values:
            values.append(integer(self.constant).hol)
        return join("+", values, "")


@dataclass(frozen=True)
class Expr:
    hol: str
    sort: str
    constant: int | None = None
    linear: Linear | None = None


def integer(value: int) -> Expr:
    # Never emit an untyped numeral: HOL numerals are polymorphic.
    text = str(value) if value >= 0 else f"(- {abs(value)})"
    return Expr(f"({text} :: int)", "Int", value, Linear(value))


def typed(value: Expr, expected: str) -> Expr:
    if value.sort != expected:
        raise Unsupported(f"expected {expected}, got {value.sort}")
    return value


def join(operator: str, values: list[str], identity: str) -> str:
    return "(" + f" {operator} ".join(values) + ")" if values else identity


class Query:
    def __init__(self, source: str):
        self.source = source
        self.free: dict[str, Expr] = {}
        self.assertions: list[Expr] = []
        self.serial = 0
        # Hints select lemmas to prove; they never replace the original goal.
        self.normalizations: dict[str, str] = {}
        checked = exited = False
        for command in parse(source):
            if not isinstance(command, list) or not command:
                raise Unsupported("expected command")
            op = keyword(command[0])
            args = command[1:]
            if exited:
                raise Unsupported("command after exit")
            if op == "check-sat" and not args and not checked:
                checked = True
            elif op in {"get-model", "get-proof", "exit"} and not args and checked:
                exited = op == "exit"
            elif checked:
                raise Unsupported("only one query, without subsequent mutations, is supported")
            elif op == "set-logic" and len(args) == 1 and keyword(args[0]) in {"LIA", "QF_LIA", "ALL"}:
                pass
            elif op == "set-info" and len(args) == 2:
                pass  # :status is never used as evidence.
            elif op == "set-option" and len(args) == 2 and keyword(args[0]) in {
                    ":produce-models", ":produce-proofs", ":print-success"} and keyword(args[1]) in {
                    "true", "false"}:
                pass
            elif op == "declare-const" and len(args) == 2:
                self.declare(args[0], args[1])
            elif op == "declare-fun" and len(args) == 3 and args[1] == []:
                self.declare(args[0], args[2])
            elif op == "assert" and len(args) == 1:
                self.assertions.append(typed(self.term(args[0], self.free), "Bool"))
            else:
                raise Unsupported(f"unsupported or malformed command: {op}")
        if not checked:
            raise Unsupported("missing check-sat")

    def fresh(self, kind: str) -> Expr:
        name = f"v{self.serial}"
        self.serial += 1
        return Expr(name, kind, linear=Linear(0, ((name, 1),)) if kind == "Int" else None)

    def normalization(self, left: Expr, op: str, right: Expr, original: str):
        if left.linear is None or right.linear is None:
            return
        difference = left.linear.add(right.linear.scale(-1))
        divisor = math.gcd(*(c for _, c in difference.coefficients))
        if divisor <= 1:
            return
        if op in {"=", "distinct"} and difference.constant % divisor:
            normalized = "False" if op == "=" else "True"
        else:
            if op in {">", ">="}:
                difference = difference.scale(-1)
            constant = difference.constant + (op in {"<", ">"})
            # ceil(c/g), including negative c: integer bounds must round up.
            reduced = Linear(-(-constant // divisor),
                             tuple((n, c // divisor) for n, c in difference.coefficients))
            relation = {"=": "=", "distinct": r"\<noteq>"}.get(op, r"\<le>")
            normalized = f"({reduced.hol()} {relation} (0 :: int))"
        self.normalizations[original] = normalized

    def declare(self, name, kind):
        name = symbol(name)
        if name in self.free:
            raise Unsupported("duplicate declaration")
        self.free[name] = self.fresh(sort(kind))

    def term(self, node, env: dict[str, Expr]) -> Expr:
        if isinstance(node, Atom):
            if node.kind == "symbol":
                if re.fullmatch(r"[0-9]+", node.text):
                    return integer(int(node.text))
                if node.text in {"true", "false"}:
                    return Expr(node.text.capitalize(), "Bool")
            name = symbol(node)
            if name not in env:
                raise Unsupported("undeclared symbol")
            return env[name]
        if not node:
            raise Unsupported("empty term")
        if isinstance(node[0], list):
            indexed = node[0]
            if (len(indexed) != 3 or indexed[:2] != [Atom("_"), Atom("divisible")] or
                    len(node) != 2 or not isinstance(indexed[2], Atom) or
                    indexed[2].kind != "symbol" or
                    not re.fullmatch(r"[1-9][0-9]*", indexed[2].text)):
                raise Unsupported("unsupported or malformed indexed operator")
            argument = typed(self.term(node[1], env), "Int")
            modulus = integer(int(indexed[2].text))
            return Expr(f"({modulus.hol} dvd {argument.hol})", "Bool")
        op, args = keyword(node[0]), node[1:]
        if op in {"forall", "exists", "let"}:
            if len(args) != 2 or not isinstance(args[0], list) or not args[0]:
                raise Unsupported("malformed binder")
            local, names, bound = dict(env), set(), []
            for binding in args[0]:
                if not isinstance(binding, list) or len(binding) != 2:
                    raise Unsupported("malformed binding")
                name = symbol(binding[0])
                if name in names:
                    raise Unsupported("duplicate binder")
                names.add(name)
                # SMT let is simultaneous: every RHS sees the outer scope.
                value = self.term(binding[1], env) if op == "let" else self.fresh(sort(binding[1]))
                local[name] = value
                bound.append(value)
            body = self.term(args[1], local)
            if op == "let":
                return body
            typed(body, "Bool")
            quantifier = r"\<forall>" if op == "forall" else r"\<exists>"
            for value in reversed(bound):
                body = Expr(f"({quantifier}{value.hol} :: {value.sort.lower()}. {body.hol})", "Bool")
            return body
        if op == "!":
            # Annotations are syntactic metadata; accept only :named, not
            # arbitrary extensions that could hide an unsupported term.
            if len(args) != 3 or keyword(args[1]) != ":named":
                raise Unsupported("unsupported term annotation")
            symbol(args[2])
            return self.term(args[0], env)
        values = [self.term(arg, env) for arg in args]
        if op in {"+", "-", "*", "div", "mod", "abs"}:
            for value in values:
                typed(value, "Int")
            if op in {"+", "*"} and len(values) >= 2:
                constants = [value.constant for value in values]
                if op == "*" and sum(c is None for c in constants) > 1:
                    raise Unsupported("nonlinear multiplication")
                if all(c is not None for c in constants):
                    result = 0 if op == "+" else 1
                    for c in constants:
                        result = result + c if op == "+" else result * c
                    return integer(result)
                linear = None
                if all(v.linear is not None for v in values):
                    linear = Linear() if op == "+" else Linear(1)
                    for value in values:
                        if op == "+":
                            linear = linear.add(value.linear)
                        elif value.constant is not None:
                            linear = linear.scale(value.constant)
                        else:
                            linear = value.linear.scale(linear.constant)
                return Expr(join(op, [v.hol for v in values], ""), "Int", linear=linear)
            if op == "-" and values:
                if all(v.constant is not None for v in values):
                    return integer(-values[0].constant if len(values) == 1 else
                                   values[0].constant - sum(v.constant for v in values[1:]))
                linear = None
                if all(v.linear is not None for v in values):
                    linear = values[0].linear.scale(-1) if len(values) == 1 else values[0].linear
                    for value in values[1:]:
                        linear = linear.add(value.linear.scale(-1))
                return Expr(f"(- {values[0].hol})" if len(values) == 1 else
                            join("-", [v.hol for v in values], ""), "Int", linear=linear)
            if op == "abs" and len(values) == 1:
                return integer(abs(values[0].constant)) if values[0].constant is not None else \
                    Expr(f"(abs {values[0].hol})", "Int")
            if (op == "div" and len(values) >= 2) or (op == "mod" and len(values) == 2):
                result = values[0]
                for operand in values[1:]:
                    divisor = operand.constant
                    if divisor is None or divisor == 0:
                        raise Unsupported("division requires a constant nonzero divisor")
                    # SMT-LIB div associates left and uses a nonnegative
                    # remainder even for negative divisors. HOL uses |d|.
                    base = f"({result.hol} {op} {integer(abs(divisor)).hol})"
                    if result.constant is not None:
                        q, r = divmod(result.constant, abs(divisor))
                        result = integer((q if divisor > 0 else -q) if op == "div" else r)
                    else:
                        result = Expr(f"(- {base})" if op == "div" and divisor < 0 else base, "Int")
                return result
            raise Unsupported("invalid arithmetic arity")
        if op in {"not", "and", "or", "=>", "xor"}:
            for value in values:
                typed(value, "Bool")
            if op == "not" and len(values) == 1:
                return Expr(r"(\<not> " + values[0].hol + ")", "Bool")
            if op in {"and", "or"} and len(values) >= 2:
                return Expr(join(r"\<and>" if op == "and" else r"\<or>",
                                 [v.hol for v in values], ""), "Bool")
            if op in {"=>", "xor"} and len(values) >= 2:
                # => is right-associative; xor is left-associative.
                if op == "=>":
                    result = values[-1].hol
                    for value in reversed(values[:-1]):
                        result = f"({value.hol} " + r"\<longrightarrow> " + result + ")"
                else:
                    result = values[0].hol
                    for value in values[1:]:
                        result = f"({result} " + r"\<noteq> " + value.hol + ")"
                return Expr(result, "Bool")
            raise Unsupported("invalid Boolean arity")
        if op in {"=", "distinct", "<", "<=", ">", ">="} and len(values) >= 2:
            for value in values:
                typed(value, values[0].sort if op in {"=", "distinct"} else "Int")
            operator = {"=": "=", "distinct": r"\<noteq>", "<": "<",
                        "<=": r"\<le>", ">": ">", ">=": r"\<ge>"}[op]
            pairs = ((values[i], values[j]) for i in range(len(values))
                     for j in range(i + 1, len(values))) if op == "distinct" else zip(values, values[1:])
            relations = []
            for a, b in pairs:
                original = f"({a.hol} {operator} {b.hol})"
                self.normalization(a, op, b, original)
                relations.append(original)
            return Expr(join(r"\<and>", relations, "True"), "Bool")
        if op == "ite" and len(values) == 3:
            typed(values[0], "Bool")
            typed(values[2], values[1].sort)
            return Expr(f"(if {values[0].hol} then {values[1].hol} else {values[2].hol})",
                        values[1].sort)
        raise Unsupported(f"unsupported operator or arity: {op}")

    def proposition(self, verdict: str, model: dict | None = None) -> str:
        if verdict not in {"sat", "unsat"}:
            raise Unsupported("only definite verdicts have proof obligations")
        body = join(r"\<and>", [a.hol for a in self.assertions], "True")
        if model is not None:
            if verdict != "sat" or set(model) != set(self.free):
                raise Unsupported("model must assign exactly the free symbols of a SAT query")
            for name, value in reversed(list(self.free.items())):
                item = model[name]
                if value.sort == "Bool" and type(item) is bool:
                    assigned = str(item)
                elif value.sort == "Int" and type(item) is int:
                    assigned = integer(item).hol
                else:
                    raise Unsupported("ill-typed model assignment")
                body = f"(let {value.hol} = {assigned} in {body})"
        else:
            for value in reversed(list(self.free.values())):
                body = r"(\<exists>" + f"{value.hol} :: {value.sort.lower()}. {body})"
        return r"(\<not> " + body + ")" if verdict == "unsat" else body

    def theory(self, verdict: str, model: dict | None = None, name="PA_Query", certificate=None) -> str:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
            raise Unsupported("invalid theory name")
        proposition = self.proposition(verdict, model)
        qe_lemmas, qe_names = pa_trace.obligations(certificate, verdict) if certificate is not None else ("", [])
        qe_dependencies = "".join(" " + item for item in qe_names)
        lemmas = "\n".join(
            f'lemma normalize_{i}: "({original}) = ({normalized})"\n'
            '  by (simp; presburger)\n'
            for i, (original, normalized) in enumerate(self.normalizations.items()))
        hints = "".join(f" normalize_{i}" for i in range(len(self.normalizations)))
        # The oracle check traverses transitive proof dependencies, including
        # skip_proof. No solver certificate or user-supplied ML is trusted.
        return f'''theory {name}
  imports "HOL.Presburger"
begin

{lemmas}
{qe_lemmas}
lemma result: "{proposition}"
  by ((simp add: Let_def all_bool_eq ex_bool_eq{hints}; fail) | (presburger add: Let_def all_bool_eq ex_bool_eq{hints}))

ML \\<open>
  val _ = if null (Thm_Deps.all_oracles @{{thms result{hints}{qe_dependencies}}}) then ()
          else error "PA theorem has oracle dependencies";
\\<close>

end
'''


def bundle(source: str, verdict: str, output: Path, model: dict | None = None,
           name="PA_Query", certificate=None):
    query = Query(source)
    output.mkdir(parents=True, exist_ok=False)
    theory = query.theory(verdict, model, name, certificate)
    (output / "input.smt2").write_text(source)
    (output / f"{name}.thy").write_text(theory)
    (output / "ROOT").write_text(
        'session Xolver_PA = HOL +\n  options [document = false, quick_and_dirty = false]\n'
        f'  theories {name}\n')
    record = {"schema": "xolver-pa-isabelle/1", "status": "generated-unchecked",
              "verdict": verdict, "model": model,
              "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "theory_sha256": hashlib.sha256(theory.encode()).hexdigest(),
              "translator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "trust_boundary": "SMT-LIB translation and HOL semantics; no C++ refinement theorem"}
    if certificate is not None:
        data = json.dumps(certificate, indent=2) + "\n"
        (output / "certificate.json").write_text(data)
        record.update(certificate_sha256=hashlib.sha256(data.encode()).hexdigest(),
                      qe_steps=len(certificate["steps"]),
                      certificate_translator_sha256=hashlib.sha256(Path(pa_trace.__file__).read_bytes()).hexdigest(),
                      certificate_scope="All supplied QE equations plus an independent original-query theorem; native lowering/composition not proved")
    (output / "claim.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--verdict", required=True, choices=["sat", "unsat"])
    parser.add_argument("--model", type=Path, help="JSON object with integer/Boolean assignments")
    parser.add_argument("--certificate", type=Path, help="native QE obligations JSON")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        model = json.loads(args.model.read_text()) if args.model else None
        certificate = pa_trace.load(args.certificate.read_text()) if args.certificate else None
        print(json.dumps(bundle(args.input.read_text(), args.verdict, args.output, model, certificate=certificate)))
    except (Unsupported, pa_trace.InvalidTrace, RecursionError) as error:
        parser.exit(2, f"unsupported input: {error}\n")


if __name__ == "__main__":
    main()
