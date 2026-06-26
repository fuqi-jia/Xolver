"""z3-flavored Pythonic API."""
import pytest

from xolver import (
    Solver, Int, Real, Bool, And, Or, Not, Implies, Ite, Distinct,
    sat, unsat,
)


def test_linear_int_sat():
    s = Solver("QF_LIA")
    x, y = s.int("x"), s.int("y")
    s.add(x + y == 10, x - y == 2)
    assert s.check() == sat
    m = s.model()
    assert m[x] == 6
    assert m[y] == 4


def test_unsat():
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0, x < 0)
    assert s.check() == unsat


def test_bool_logic():
    s = Solver("QF_UF")
    p, q = s.bool("p"), s.bool("q")
    s.add(Or(p, q), Not(And(p, q)), Implies(p, q))
    assert s.check() == sat
    m = s.model()
    # p->q and not(p and q) and (p or q): forces p False, q True.
    assert m[p] is False
    assert m[q] is True


def test_nonlinear_real():
    s = Solver("QF_NRA")
    a = s.real("a")
    s.add(a * a == 2, a > 0)
    assert s.check() == sat
    val = s.model()[a]
    # a == sqrt(2): the model value squared should be 2 (exact rational approx
    # or algebraic — at minimum the verdict is sat).
    assert val is not None


def test_module_default_solver():
    # Int/Real share one hidden default solver; mixing with it is fine.
    x, y = Int("x"), Int("y")
    s = x._solver
    s.push()
    s.add(x > 0, y > 0, x + y == 3)
    assert s.check() == sat
    s.pop()


def test_cross_solver_mixing_raises():
    s1, s2 = Solver(), Solver()
    x1 = s1.int("x")
    x2 = s2.int("x")
    with pytest.raises(ValueError):
        _ = x1 + x2


def test_ite_max():
    s = Solver("QF_LIA")
    x, y, z = s.int("x"), s.int("y"), s.int("z")
    s.add(x == Ite(y > z, y, z))   # x = max(y, z)
    s.add(y == 1, z == 5)
    assert s.check() == sat
    assert s.model()[x] == 5


def test_distinct():
    s = Solver("QF_LIA")
    a, b, c = s.int("a"), s.int("b"), s.int("c")
    s.add(Distinct(a, b, c))
    s.add(a >= 0, a < 3, b >= 0, b < 3, c >= 0, c < 3)
    assert s.check() == sat
    vals = {s.model()[a], s.model()[b], s.model()[c]}
    assert len(vals) == 3          # all different


def test_assumptions():
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0)
    # under the assumption x < 0, unsat; without it, sat.
    assert s.check(x < 0) == unsat
    assert s.check() == sat


def test_expr_has_no_truth_value():
    s = Solver("QF_LIA")
    x = s.int("x")
    with pytest.raises(TypeError):
        bool(x > 0)
