"""A z3-flavored, Pythonic surface over the low-level ``_xolver`` binding.

Example::

    from xolver import Int, Real, And, solve
    x, y = Int('x'), Int('y')
    solve(x + y == 10, x - y == 2)          # -> [x = 6, y = 4]

    from xolver import Solver, Real
    s = Solver()
    a, b = s.real('a'), s.real('b')
    s.add(a * a + b * b < 1, a > 0)
    if s.check() == 'sat':
        print(s.model())

Design note (differs from z3): a :class:`Solver` is *also* the term factory —
``Term`` ids index a single solver's IR, so a term made on one solver cannot be
asserted on another. Module-level helpers (``Int``/``Real``/``Bool``/``solve``)
use one hidden default solver; the explicit ``Solver()`` style keeps everything
on that instance. Mixing the two raises a clear error.
"""

from __future__ import annotations

import re
from fractions import Fraction
from typing import Iterable, Optional, Union

from . import _xolver
from ._xolver import Kind, Result

# z3-style result sentinels.
sat = Result.Sat
unsat = Result.Unsat
unknown = Result.Unknown

# Python values acceptable where an expression is expected.
PyNum = Union[int, float, "Fraction", bool, str]
Coercible = Union["ExprRef", PyNum]

__all__ = [
    "Solver", "ExprRef", "ModelRef",
    "Int", "Real", "Bool", "IntVal", "RealVal", "BoolVal",
    "And", "Or", "Not", "Implies", "Xor", "Ite", "If", "Distinct",
    "solve", "sat", "unsat", "unknown", "Result", "Kind",
]


# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------
class ExprRef:
    """A solver term plus a light sort tag ('Int'|'Real'|'Bool'|'BV'|...).

    Created via :class:`Solver` factories or the module-level helpers; you build
    formulas with Python operators (``x + y``, ``x <= 3``, ``(x > 0) & p``).
    """

    __slots__ = ("_solver", "_term", "_sort")

    def __init__(self, solver: "Solver", term, sort: str):
        self._solver = solver
        self._term = term
        self._sort = sort

    # --- introspection ---
    @property
    def solver(self) -> "Solver":
        return self._solver

    @property
    def term(self):
        return self._term

    @property
    def sort(self) -> str:
        return self._sort

    def __repr__(self) -> str:
        return f"<xolver.ExprRef {self._sort} id={self._term.id()}>"

    # --- coercion ---
    def _coerce(self, other: Coercible) -> "ExprRef":
        if isinstance(other, ExprRef):
            if other._solver is not self._solver:
                raise ValueError(
                    "cannot combine terms from different Solver instances; "
                    "create both on the same solver (or use the module-level "
                    "Int/Real/Bool which share one default solver)")
            return other
        # Coerce a Python literal into the sort of `self`.
        return self._solver._literal_like(self._sort, other)

    def _binop(self, kind: Kind, other: Coercible, result_sort: str) -> "ExprRef":
        o = self._coerce(other)
        t = self._solver._s.mk_op(kind, [self._term, o._term])
        return ExprRef(self._solver, t, result_sort)

    def _rbinop(self, kind: Kind, other: Coercible, result_sort: str) -> "ExprRef":
        o = self._coerce(other)
        t = self._solver._s.mk_op(kind, [o._term, self._term])
        return ExprRef(self._solver, t, result_sort)

    # --- arithmetic (result sort inherits from self) ---
    def __add__(self, o): return self._binop(Kind.Add, o, self._sort)
    def __radd__(self, o): return self._rbinop(Kind.Add, o, self._sort)
    def __sub__(self, o): return self._binop(Kind.Sub, o, self._sort)
    def __rsub__(self, o): return self._rbinop(Kind.Sub, o, self._sort)
    def __mul__(self, o): return self._binop(Kind.Mul, o, self._sort)
    def __rmul__(self, o): return self._rbinop(Kind.Mul, o, self._sort)
    def __truediv__(self, o): return self._binop(Kind.Div, o, self._sort)
    def __rtruediv__(self, o): return self._rbinop(Kind.Div, o, self._sort)
    def __mod__(self, o): return self._binop(Kind.Mod, o, self._sort)
    def __rmod__(self, o): return self._rbinop(Kind.Mod, o, self._sort)

    def __neg__(self):
        t = self._solver._s.mk_op(Kind.Neg, [self._term])
        return ExprRef(self._solver, t, self._sort)

    def __pos__(self):
        return self

    # --- comparisons (result sort Bool) ---
    def __lt__(self, o): return self._binop(Kind.Lt, o, "Bool")
    def __le__(self, o): return self._binop(Kind.Leq, o, "Bool")
    def __gt__(self, o): return self._binop(Kind.Gt, o, "Bool")
    def __ge__(self, o): return self._binop(Kind.Geq, o, "Bool")

    def __eq__(self, o):  # noqa: D105 — builds an Eq term, not a Python bool
        return self._binop(Kind.Eq, o, "Bool")

    def __ne__(self, o):
        return self._binop(Kind.Distinct, o, "Bool")

    def __hash__(self):
        return self._term.id()

    # --- boolean operators (& | ~ on Bool exprs) ---
    def __and__(self, o): return self._binop(Kind.And, o, "Bool")
    def __rand__(self, o): return self._rbinop(Kind.And, o, "Bool")
    def __or__(self, o): return self._binop(Kind.Or, o, "Bool")
    def __ror__(self, o): return self._rbinop(Kind.Or, o, "Bool")
    def __xor__(self, o): return self._binop(Kind.Xor, o, "Bool")
    def __rxor__(self, o): return self._rbinop(Kind.Xor, o, "Bool")

    def __invert__(self):
        t = self._solver._s.mk_op(Kind.Not, [self._term])
        return ExprRef(self._solver, t, "Bool")

    def __bool__(self):
        raise TypeError(
            "an ExprRef has no Python truth value; use it in a constraint "
            "(e.g. s.add(x > 0)), not in an `if`/`and`/`or`")


# ---------------------------------------------------------------------------
# Model
# ---------------------------------------------------------------------------
class AlgebraicNumber:
    """A real-algebraic model value: a root of ``poly`` isolated in
    ``[lower, upper]``. The value is exact (poly + interval); ``approx()`` /
    ``float()`` give a rational/float midpoint for display."""

    __slots__ = ("raw", "coeffs", "lower", "upper")

    def __init__(self, raw, coeffs=None, lower=None, upper=None):
        self.raw = raw
        self.coeffs = coeffs          # poly coefficients, high degree first
        self.lower = lower            # Fraction
        self.upper = upper            # Fraction

    def approx(self):
        if self.lower is not None and self.upper is not None:
            return (self.lower + self.upper) / 2
        return None

    def __float__(self):
        a = self.approx()
        if a is None:
            raise ValueError("algebraic number has no isolating interval")
        return float(a)

    def __repr__(self):
        a = self.approx()
        body = f"root({self.coeffs}) in [{self.lower}, {self.upper}]"
        return body + (f" ~ {float(a):.9g}" if a is not None else "")


_ALG_RE = re.compile(
    r"\(AlgebraicNumber\s+\(poly\s+([-\d\s]+)\)\s+"
    r"\(lower\s+(\S+)\)\s+\(upper\s+(\S+)\)\s*\)", re.DOTALL)


def _parse_value(tok):
    """Parse an Xolver model value string into a Python value."""
    if tok is None:
        return None
    tok = tok.strip()
    if tok == "true":
        return True
    if tok == "false":
        return False
    # Real-algebraic value: (AlgebraicNumber (poly ...) (lower L) (upper U))
    m = _ALG_RE.fullmatch(tok)
    if m:
        coeffs = [int(c) for c in m.group(1).split()]
        return AlgebraicNumber(tok, coeffs, _frac(m.group(2)), _frac(m.group(3)))
    # (- N)
    m = re.fullmatch(r"\(\s*-\s+(.+?)\s*\)", tok, re.DOTALL)
    if m:
        v = _parse_value(m.group(1))
        return -v if isinstance(v, (int, Fraction)) else tok
    # (/ a b)
    m = re.fullmatch(r"\(\s*/\s+(\S+)\s+(\S+)\s*\)", tok, re.DOTALL)
    if m:
        return Fraction(_frac(m.group(1))) / Fraction(_frac(m.group(2)))
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)
    if re.fullmatch(r"-?\d+/\d+", tok):          # plain rational p/q
        return Fraction(tok)
    if re.fullmatch(r"-?\d+\.\d+", tok):
        return Fraction(tok)
    return tok                                    # leave anything else raw


def _frac(tok: str):
    tok = tok.strip()
    if re.fullmatch(r"-?\d+/\d+", tok) or re.fullmatch(r"-?\d+", tok):
        return Fraction(tok)
    return Fraction(tok)


class ModelRef:
    """A satisfying assignment, read back from the low-level model (keyed by
    term id, so it works for programmatically-built terms). Index by an
    :class:`ExprRef` (``m[x]``) or by a declared name (``m['x']``)."""

    def __init__(self, ll_model, consts):
        self._m = ll_model            # _xolver.Model
        self._consts = consts         # name -> ExprRef (declared on the solver)

    def _expr(self, key):
        if isinstance(key, ExprRef):
            return key
        if isinstance(key, str):
            return self._consts.get(key)
        return None

    def __getitem__(self, key):
        e = self._expr(key)
        if e is None:
            raise KeyError(key)
        v = self._m.get_value(e.term.id())
        if v is None:
            raise KeyError(key)
        return _parse_value(v)

    def eval(self, key):
        return self[key]

    def get(self, key, default=None):
        try:
            return self[key]
        except KeyError:
            return default

    def __contains__(self, key) -> bool:
        try:
            self[key]
            return True
        except KeyError:
            return False

    def names(self):
        return [n for n, e in self._consts.items()
                if self._m.get_value(e.term.id()) is not None]

    def __iter__(self):
        for name in self.names():
            yield name, self[name]

    def __repr__(self) -> str:
        return "[" + ", ".join(f"{n} = {v}" for n, v in self) + "]"


# A named const remembers its name for model lookup.
class _NamedExpr(ExprRef):
    __slots__ = ("_name",)

    def __init__(self, solver, term, sort, name):
        super().__init__(solver, term, sort)
        self._name = name


# ---------------------------------------------------------------------------
# Solver
# ---------------------------------------------------------------------------
class Solver:
    """A Pythonic solver that is also the term factory."""

    def __init__(self, logic: Optional[str] = None):
        self._s = _xolver.Solver()
        self._sorts = {}
        self._consts = {}          # name -> ExprRef, for model read-back
        self._propagator = None    # keep a Python ref alive while registered
        if logic:
            self.set_logic(logic)

    # --- config ---
    def set_logic(self, logic: str):
        self._s.set_logic(logic)
        return self

    def set_option(self, key: str, value):
        self._s.set_option(key, value)
        return self

    # --- sorts (cached) ---
    def _bool_sort(self):
        s = self._sorts.get("Bool")
        if s is None:
            s = self._sorts["Bool"] = self._s.bool_sort()
        return s

    def _int_sort(self):
        s = self._sorts.get("Int")
        if s is None:
            s = self._sorts["Int"] = self._s.int_sort()
        return s

    def _real_sort(self):
        s = self._sorts.get("Real")
        if s is None:
            s = self._sorts["Real"] = self._s.real_sort()
        return s

    # --- const factories ---
    def _declare(self, name: str, sort: str, ll_sort) -> ExprRef:
        e = _NamedExpr(self, self._s.mk_const(ll_sort, name), sort, name)
        self._consts[name] = e
        return e

    def int(self, name: str) -> ExprRef:
        return self._declare(name, "Int", self._int_sort())

    def real(self, name: str) -> ExprRef:
        return self._declare(name, "Real", self._real_sort())

    def bool(self, name: str) -> ExprRef:
        return self._declare(name, "Bool", self._bool_sort())

    # aliases mirroring z3 spelling
    int_const = int
    real_const = real
    bool_const = bool

    # --- literals ---
    def int_val(self, v: int) -> ExprRef:
        return ExprRef(self, self._s.mk_int(int(v)), "Int")

    def real_val(self, v: PyNum) -> ExprRef:
        return ExprRef(self, self._s.mk_real(_to_rational(v)), "Real")

    def bool_val(self, v: bool) -> ExprRef:
        return ExprRef(self, self._s.mk_bool(bool(v)), "Bool")

    def _literal_like(self, sort: str, v: Coercible) -> ExprRef:
        if isinstance(v, ExprRef):
            return v
        if sort == "Bool" or isinstance(v, bool):
            return self.bool_val(bool(v))
        if sort == "Real":
            return self.real_val(v)
        if sort == "Int" and isinstance(v, int):
            return self.int_val(v)
        # Fall back to a real for non-integers in an Int/unknown context.
        if isinstance(v, int):
            return self.int_val(v)
        return self.real_val(v)

    # --- assertions / solving ---
    def add(self, *constraints: Union[ExprRef, Iterable[ExprRef]]):
        for c in _flatten(constraints):
            if not isinstance(c, ExprRef):
                raise TypeError(f"expected an ExprRef constraint, got {type(c)!r}")
            if c._solver is not self:
                raise ValueError("constraint belongs to a different Solver")
            self._s.assert_formula(c._term)
        return self

    assert_ = add

    def check(self, *assumptions: ExprRef) -> Result:
        if assumptions:
            terms = []
            for a in _flatten(assumptions):
                if a._solver is not self:
                    raise ValueError("assumption belongs to a different Solver")
                terms.append(a._term)
            return self._s.check_sat_assuming(terms)
        return self._s.check_sat()

    def model(self) -> ModelRef:
        return ModelRef(self._s.get_model(), self._consts)

    def value(self, e: ExprRef):
        """Value of a const in the current model (Python value)."""
        return self.model()[e]

    def to_smt2_model(self) -> str:
        """The raw SMT-LIB get-model response (populated for parsed input)."""
        return self._s.dump_model()

    def push(self):
        self._s.push()
        return self

    def pop(self, n: int = 1):
        self._s.pop(n)
        return self

    def reset(self):
        self._s.reset()
        self._sorts.clear()
        self._consts.clear()
        return self

    def set_propagator(self, p):
        """Register a one-step user :class:`xolver.Propagator` (or None to
        detach). Observe/steer the CDCL(T) search; sound by construction."""
        self._propagator = p
        self._s.set_propagator(p) if p is not None else self._s.clear_propagator()
        return self

    def reason_unknown(self) -> str:
        return self._s.last_unknown_reason()

    def to_smt2(self) -> str:
        return self._s.dump_smt2()

    @property
    def raw(self):
        """The underlying low-level ``_xolver.Solver`` (escape hatch)."""
        return self._s


# ---------------------------------------------------------------------------
# Module-level helpers (default solver)
# ---------------------------------------------------------------------------
_default: Optional[Solver] = None


def _ds() -> Solver:
    global _default
    if _default is None:
        _default = Solver()
    return _default


def Int(name: str) -> ExprRef: return _ds().int(name)
def Real(name: str) -> ExprRef: return _ds().real(name)
def Bool(name: str) -> ExprRef: return _ds().bool(name)
def IntVal(v: int) -> ExprRef: return _ds().int_val(v)
def RealVal(v: PyNum) -> ExprRef: return _ds().real_val(v)
def BoolVal(v: bool) -> ExprRef: return _ds().bool_val(v)


def _nary(kind: Kind, args, sort: str) -> ExprRef:
    args = list(_flatten(args))
    if not args:
        raise ValueError("need at least one argument")
    exprs = [a for a in args if isinstance(a, ExprRef)]
    if not exprs:
        raise TypeError("need at least one ExprRef argument")
    solver = exprs[0]._solver
    terms = []
    for a in args:
        e = a if isinstance(a, ExprRef) else solver._literal_like(sort, a)
        if e._solver is not solver:
            raise ValueError("arguments come from different Solver instances")
        terms.append(e._term)
    return ExprRef(solver, solver._s.mk_op(kind, terms), sort)


def And(*args) -> ExprRef: return _nary(Kind.And, args, "Bool")
def Or(*args) -> ExprRef: return _nary(Kind.Or, args, "Bool")
def Distinct(*args) -> ExprRef: return _nary(Kind.Distinct, args, "Bool")


def Not(a: ExprRef) -> ExprRef:
    return ExprRef(a._solver, a._solver._s.mk_op(Kind.Not, [a._term]), "Bool")


def Implies(a: ExprRef, b: Coercible) -> ExprRef:
    return a._binop(Kind.Implies, b, "Bool")


def Xor(a: ExprRef, b: Coercible) -> ExprRef:
    return a._binop(Kind.Xor, b, "Bool")


def Ite(cond: ExprRef, then_: ExprRef, else_: ExprRef) -> ExprRef:
    solver = cond._solver
    t = then_ if isinstance(then_, ExprRef) else solver._literal_like("Int", then_)
    e = else_ if isinstance(else_, ExprRef) else solver._literal_like(t._sort, else_)
    term = solver._s.mk_op(Kind.Ite, [cond._term, t._term, e._term])
    return ExprRef(solver, term, t._sort)


If = Ite  # z3 spelling


def solve(*constraints) -> None:
    """Quick z3-style solve: add the constraints to the default solver, check,
    and print the model (or unsat/unknown)."""
    s = _ds()
    s.push()
    try:
        s.add(*constraints)
        r = s.check()
        if r == sat:
            print(s.model())
        elif r == unsat:
            print("no solution")
        else:
            print("unknown:", s.reason_unknown())
    finally:
        s.pop()


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------
def _flatten(items):
    for it in items:
        if isinstance(it, ExprRef):
            yield it
        elif isinstance(it, (list, tuple, set, frozenset)) or (
            hasattr(it, "__iter__") and not isinstance(it, (str, bytes))
        ):
            yield from _flatten(it)
        else:
            yield it


def _to_rational(v: PyNum) -> str:
    """Render a Python number as an SMT-LIB rational string ('p/q' or 'n')."""
    if isinstance(v, str):
        return v
    if isinstance(v, bool):
        return "1" if v else "0"
    if isinstance(v, int):
        return str(v)
    fr = Fraction(v).limit_denominator(10**12) if isinstance(v, float) else Fraction(v)
    return f"{fr.numerator}/{fr.denominator}" if fr.denominator != 1 else str(fr.numerator)
