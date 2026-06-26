"""Xolver Python quickstart — z3-flavored usage.

Run after `pip install xolver` (or, from a source build, with the build dir on
PYTHONPATH):  python python/examples/quickstart.py
"""
from xolver import Int, Real, Solver, And, Or, Not, Implies, Ite, Distinct, solve


def linear_integers():
    print("== linear integers ==")
    x, y = Int("x"), Int("y")
    solve(x + y == 10, x - y == 2)            # [x = 6, y = 4]


def a_little_logic():
    print("== boolean logic ==")
    s = Solver("QF_UF")
    p, q, r = s.bool("p"), s.bool("q"), s.bool("r")
    s.add(Or(p, q, r), Implies(p, q), Not(And(q, r)))
    print(s.check(), s.model())


def nonlinear_real():
    print("== nonlinear real: a^2 == 2, a > 0 ==")
    s = Solver("QF_NRA")
    a = s.real("a")
    s.add(a * a == 2, a > 0)
    print(s.check())
    print(s.model())                          # an algebraic value for sqrt(2)


def a_max_with_ite():
    print("== x = max(y, z) via Ite ==")
    s = Solver("QF_LIA")
    x, y, z = s.int("x"), s.int("y"), s.int("z")
    s.add(x == Ite(y > z, y, z), y == 3, z == 8)
    print(s.check(), s.model())               # x = 8


def incremental():
    print("== incremental push/pop + assumptions ==")
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0)
    print("x>0 :", s.check())                 # sat
    print("assume x<0 :", s.check(x < 0))     # unsat (assumption only)
    print("still :", s.check())               # sat (assumption discarded)


if __name__ == "__main__":
    linear_integers()
    a_little_logic()
    nonlinear_real()
    a_max_with_ite()
    incremental()
