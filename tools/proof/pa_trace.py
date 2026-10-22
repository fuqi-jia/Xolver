#!/usr/bin/env python3
"""Validate native PA QE obligations and translate them to HOL equations.

This is a data parser, not a proof checker. Every equation must be proved by
Isabelle. The original SMT query is proved separately: the ledger does not yet
certify native input lowering or composition of quantifier/Boolean contexts.
"""
from __future__ import annotations

import json
import re


class InvalidTrace(ValueError):
    pass


def load(source: str) -> dict:
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise InvalidTrace("duplicate certificate key")
            result[key] = value
        return result
    return json.loads(source, object_pairs_hook=object_pairs)


def fields(value, expected):
    if type(value) is not dict or set(value) != set(expected):
        raise InvalidTrace("invalid certificate fields")


def variable(value):
    if type(value) is not str or not re.fullmatch(r"0|[1-9][0-9]{0,19}", value):
        raise InvalidTrace("invalid variable id")
    if int(value) >= 2**64:
        raise InvalidTrace("variable id overflow")
    return "qe_v" + value


def integer(value):
    if type(value) is not str or not re.fullmatch(r"0|-?[1-9][0-9]*", value):
        raise InvalidTrace("noncanonical exact integer")
    return f"(- ({value[1:]}::int))" if value.startswith("-") else f"({value}::int)"


def formula(value):
    if type(value) is not list:
        raise InvalidTrace("DNF must be a list")
    cubes, variables = [], set()
    for cube in value:
        if type(cube) is not list:
            raise InvalidTrace("cube must be a list")
        atoms = []
        for atom in cube:
            fields(atom, ("coefficients", "constant", "divisor", "negated"))
            if type(atom["coefficients"]) is not list or type(atom["negated"]) is not bool:
                raise InvalidTrace("invalid affine literal")
            terms = [integer(atom["constant"])]
            seen = set()
            for pair in atom["coefficients"]:
                if type(pair) is not list or len(pair) != 2:
                    raise InvalidTrace("invalid coefficient pair")
                name, coefficient = variable(pair[0]), integer(pair[1])
                if name in seen or pair[1] == "0":
                    raise InvalidTrace("duplicate or zero coefficient")
                seen.add(name)
                variables.add(name)
                terms.append(f"({coefficient} * ({name}::int))")
            affine = "(" + " + ".join(terms) + ")"
            divisor = integer(atom["divisor"])
            if atom["divisor"].startswith("-"):
                raise InvalidTrace("negative divisibility modulus")
            if atom["divisor"] == "0":
                if atom["negated"]:
                    raise InvalidTrace("inequality has divisibility negation")
                predicate = f"({affine} \\<le> 0)"
            else:
                predicate = f"({divisor} dvd {affine})"
                if atom["negated"]:
                    predicate = r"(\<not> " + predicate + ")"
            atoms.append(predicate)
        cubes.append("(" + r" \<and> ".join(atoms) + ")" if atoms else "True")
    return ("(" + r" \<or> ".join(cubes) + ")" if cubes else "False"), variables


def obligations(trace: dict, verdict: str):
    fields(trace, ("schema", "status", "verdict", "steps", "closed", "step_count"))
    if (trace["schema"] != "xolver-pa-qe-obligations/1" or
            trace["status"] != "generated-unchecked" or
            verdict not in ("sat", "unsat") or trace["verdict"] != verdict):
        raise InvalidTrace("wrong certificate schema, status or verdict")
    if (type(trace["steps"]) is not list or type(trace["step_count"]) is not int or
            trace["step_count"] != len(trace["steps"])):
        raise InvalidTrace("incomplete elimination step list")
    lemmas, names = [], []
    for i, step in enumerate(trace["steps"]):
        fields(step, ("variable", "before", "after"))
        name = variable(step["variable"])
        before, before_variables = formula(step["before"])
        after, after_variables = formula(step["after"])
        if name in after_variables or not after_variables <= before_variables:
            raise InvalidTrace("elimination leaves its variable or introduces a fresh one")
        equation = r"((\<exists>" + name + " :: int. " + before + ") = " + after + ")"
        for free in sorted((before_variables | after_variables) - {name}, reverse=True):
            equation = r"(\<forall>" + free + " :: int. " + equation + ")"
        names.append(f"qe_step_{i}")
        lemmas.append(f'lemma {names[-1]}: "{equation}"\n  by (simp; presburger)\n')
    if trace["closed"] != ([[]] if verdict == "sat" else []):
        raise InvalidTrace("decision did not close to the claimed Boolean constant")
    return "\n".join(lemmas), names
