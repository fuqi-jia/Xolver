"""Replay algebraic model constants as uniquely isolated real witnesses."""
from fractions import Fraction
from math import gcd, lcm
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


def sturm_sequence(coefficients):
    polynomial = trim(Fraction(c) for c in coefficients)
    if len(polynomial) < 2:
        raise ValueError('algebraic model requires a nonconstant polynomial')
    sequence = [polynomial, [i * polynomial[i] for i in range(1, len(polynomial))]]
    while sequence[-1]:
        residual = remainder(sequence[-2], sequence[-1])
        if not residual:
            break
        sequence.append([-c for c in residual])

    return sequence


def variations(sequence, point):
    signs = [1 if value > 0 else -1 for poly in sequence
             if (value := evaluate(poly, point)) != 0]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def isolates_unique_real_root(coefficients, lower, upper):
    """Exact Sturm count in an open rational interval, independent of Xolver."""
    polynomial = trim(Fraction(c) for c in coefficients)
    lower, upper = Fraction(lower), Fraction(upper)
    if len(polynomial) < 2 or lower >= upper:
        return False
    if evaluate(polynomial, lower) == 0 or evaluate(polynomial, upper) == 0:
        return False  # Boundary roots do not establish an open isolating interval.
    sequence = sturm_sequence(polynomial)
    return variations(sequence, lower) - variations(sequence, upper) == 1


def indexed_root_interval(coefficients, index, max_refinements=4096):
    """Isolate the indexed distinct real root in increasing, one-based order.

    Z3's display_root_smt2 uses this order; see algebraic_numbers.h under
    https://github.com/Z3Prover/z3/tree/master/src/math/polynomial .
    Counts and endpoints are exact. Failure never invents a witness.
    """
    polynomial = trim(Fraction(c) for c in coefficients)
    sequence = sturm_sequence(polynomial)
    if not isinstance(index, int) or index <= 0:
        raise ValueError('algebraic root index must be a positive integer')
    # Strictly outside Cauchy's 1 + max(|a_i/a_n|) root bound.
    bound = 2 + max(abs(c / polynomial[-1]) for c in polynomial[:-1])
    lower, upper = -bound, bound
    below, above = variations(sequence, lower), variations(sequence, upper)
    if index > below - above:
        raise ValueError('algebraic root index exceeds the number of real roots')
    for iteration in range(max_refinements + 1):
        if below - above == 1:
            return lower, upper
        if iteration == max_refinements:
            break
        # Avoid endpoint roots, including rational and repeated roots.
        for denominator in range(2, len(polynomial) + 3):
            middle = lower + (upper - lower) / denominator
            if evaluate(polynomial, middle) != 0:
                break
        else:
            raise ValueError('unable to choose a nonroot subdivision point')
        at_middle = variations(sequence, middle)
        left_roots = below - at_middle
        if index <= left_roots:
            upper, above = middle, at_middle
        else:
            lower, below, index = middle, at_middle, index - left_roots
    raise ValueError('algebraic root isolation allocation exhausted')


def root_object_polynomial(root):
    """Decode Z3's bound polynomial variable x without capturing source x."""
    memo, pending = {}, [(root, False)]

    def add(left, right):
        result = [Fraction(0)] * max(len(left), len(right))
        for i, value in enumerate(left):
            result[i] += value
        for i, value in enumerate(right):
            result[i] += value
        return trim(result)

    def multiply(left, right):
        if not left or not right:
            return []
        if len(left) + len(right) - 2 > 128:
            raise ValueError('algebraic model polynomial degree exceeds allocation')
        result = [Fraction(0)] * (len(left) + len(right) - 1)
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                result[i + j] += a * b
        return trim(result)

    while pending:
        node, ready = pending.pop()
        if id(node) in memo:
            continue
        if isinstance(node, Atom):
            memo[id(node)] = ([Fraction(0), Fraction(1)] if node.kind == 'symbol'
                              and node.text == 'x' else trim([rational(node)]))
            continue
        if not isinstance(node, list) or not node or not isinstance(node[0], Atom):
            raise ValueError('malformed algebraic model polynomial')
        if not ready:
            pending.append((node, True))
            pending.extend((child, False) for child in reversed(node[1:]))
            continue
        operation, values = node[0].text, [memo[id(child)] for child in node[1:]]
        if operation == '+' and values:
            value = []
            for term in values:
                value = add(value, term)
        elif operation == '-' and values:
            value = values[0] if len(values) > 1 else [-c for c in values[0]]
            for term in values[1:]:
                value = add(value, [-c for c in term])
        elif operation == '*' and values:
            value = [Fraction(1)]
            for term in values:
                value = multiply(value, term)
        elif operation == '/' and len(values) == 2 and len(values[1]) == 1 and values[1][0]:
            value = [c / values[1][0] for c in values[0]]
        elif operation == '^' and len(values) == 2:
            exponent = rational(node[2])
            if exponent.denominator != 1 or exponent < 0 or exponent > 128:
                raise ValueError('unsupported algebraic polynomial exponent')
            value = [Fraction(1)]
            for _ in range(exponent.numerator):
                value = multiply(value, values[0])
        else:
            raise ValueError('unsupported algebraic model polynomial operation')
        memo[id(node)] = trim(value)
    coefficients = memo[id(root)]
    if len(coefficients) < 2:
        raise ValueError('algebraic model requires a nonconstant polynomial')
    denominator = lcm(*(c.denominator for c in coefficients))
    integers = [int(c * denominator) for c in coefficients]
    divisor = gcd(*integers)
    if integers[-1] < 0:
        divisor = -divisor
    return tuple(Fraction(c // divisor) for c in integers)


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
                and node[0].text in ('root-of-with-interval', 'root-obj')):
            if node[0].text == 'root-obj':
                if 'root-obj' in source_symbols:
                    raise ValueError('algebraic model constructor collides with a source declaration')
                if len(node) != 3:
                    raise ValueError('malformed indexed algebraic model root')
                index = rational(node[2])
                if index.denominator != 1:
                    raise ValueError('algebraic root index must be a positive integer')
                coefficients = root_object_polynomial(node[1])
                lower, upper = indexed_root_interval(coefficients, index.numerator)
            else:
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
