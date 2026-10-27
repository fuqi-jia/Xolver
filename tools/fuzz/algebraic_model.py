"""Replay algebraic model constants as uniquely isolated real witnesses."""
from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'proof'))
from isabelle_pa import Atom


def rational(node):
    if isinstance(node, Atom) and node.kind == 'symbol':
        try:
            return Fraction(node.text)
        except (ValueError, ZeroDivisionError):
            pass
    if isinstance(node, list) and node and isinstance(node[0], Atom):
        if node[0].text == '-' and len(node) == 2:
            return -rational(node[1])
        if node[0].text == '/' and len(node) == 3:
            denominator = rational(node[2])
            if denominator:
                return rational(node[1]) / denominator
    raise ValueError('non-rational algebraic model endpoint or coefficient')


def trim(poly):
    poly = list(poly)
    while poly and not poly[-1]:
        poly.pop()
    return poly


def remainder(left, right):
    left = trim(left)
    while len(left) >= len(right):
        shift, scale = len(left) - len(right), left[-1] / right[-1]
        for index, coefficient in enumerate(right):
            left[index + shift] -= scale * coefficient
        left = trim(left)
    return left


def evaluate(poly, point):
    result = Fraction(0)
    for coefficient in reversed(poly):
        result = result * point + coefficient
    return result


def isolates_unique_real_root(coefficients, lower, upper):
    """Exact Sturm count in an open rational interval, independent of Xolver."""
    polynomial = trim(Fraction(c) for c in coefficients)
    lower, upper = Fraction(lower), Fraction(upper)
    if len(polynomial) < 2 or lower >= upper:
        return False
    if evaluate(polynomial, lower) == 0 or evaluate(polynomial, upper) == 0:
        return False  # Boundary roots do not establish an open isolating interval.
    sequence = [polynomial, [i * polynomial[i] for i in range(1, len(polynomial))]]
    while sequence[-1]:
        residual = remainder(sequence[-2], sequence[-1])
        if not residual:
            break
        sequence.append([-c for c in residual])

    def variations(point):
        signs = [1 if value > 0 else -1 for poly in sequence
                 if (value := evaluate(poly, point)) != 0]
        return sum(a != b for a, b in zip(signs, signs[1:]))

    return variations(lower) - variations(upper) == 1


def numeral(value):
    value = Fraction(value)
    numerator = str(value.numerator) if value >= 0 else f'(- {-value.numerator})'
    return numerator if value.denominator == 1 else f'(/ {numerator} {value.denominator})'


def expand_algebraic_roots(bindings, original_commands):
    """Return equivalent bindings and standard SMT declarations/assertions.

    Every fresh value has exactly one possible real interpretation. Original
    model expressions and all original assertions are retained around it.
    """
    reserved, source_symbols = set(), set()
    pending = list(original_commands)
    while pending:
        node = pending.pop()
        if isinstance(node, list):
            pending.extend(node)
        elif isinstance(node, Atom) and node.kind != 'string':
            source_symbols.add(node.text)
    pending = [*bindings, *original_commands]
    while pending:
        node = pending.pop()
        if isinstance(node, list):
            pending.extend(node)
        elif isinstance(node, Atom):
            reserved.add(node.text)
    prelude, memo, roots = [], {}, {}
    stack = [(binding, False) for binding in reversed(bindings)]
    while stack:
        node, processed = stack.pop()
        if not isinstance(node, list) or id(node) in memo:
            continue
        if (node and isinstance(node[0], Atom) and node[0].kind != 'string'
                and node[0].text == 'root-of-with-interval'):
            if source_symbols & {'root-of-with-interval', 'coeffs'}:
                raise ValueError('algebraic model constructor collides with a source declaration')
            if (len(node) != 4 or not isinstance(node[1], list) or len(node[1]) < 3
                    or not isinstance(node[1][0], Atom) or node[1][0].text != 'coeffs'):
                raise ValueError('malformed algebraic model root')
            coefficients = tuple(rational(c) for c in node[1][1:])
            lower, upper = rational(node[2]), rational(node[3])
            if any(c.denominator != 1 for c in coefficients):
                raise ValueError('algebraic model coefficients must be integers')
            key = coefficients, lower, upper
            if key not in roots:
                if not isolates_unique_real_root(coefficients, lower, upper):
                    raise ValueError('algebraic model interval must isolate exactly one real root')
                index = len(roots)
                symbol = f'__xolver_algebraic_witness_{index}'
                while symbol in reserved:
                    index += 1
                    symbol = f'__xolver_algebraic_witness_{index}'
                reserved.add(symbol)
                roots[key] = Atom(symbol)
                poly = numeral(coefficients[-1])
                for coefficient in reversed(coefficients[:-1]):
                    poly = f'(+ (* {poly} {symbol}) {numeral(coefficient)})'
                prelude.extend([f'(declare-const {symbol} Real)', f'(assert (= {poly} 0))',
                                f'(assert (and (< {numeral(lower)} {symbol}) (< {symbol} {numeral(upper)})))'])
            memo[id(node)] = roots[key]
        elif processed:
            memo[id(node)] = [memo[id(child)] if isinstance(child, list) else child for child in node]
        else:
            stack.append((node, True))
            stack.extend((child, False) for child in reversed(node) if isinstance(child, list))
    return [memo[id(binding)] for binding in bindings], prelude
