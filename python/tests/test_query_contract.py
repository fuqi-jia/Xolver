from fractions import Fraction
import pytest
from xolver import Solver, RawSolver, ModelValidation, Result, Kind, Term, Sort


def test_context_handles_and_nulls():
    a, b = RawSolver(), RawSolver()
    t = a.mk_bool(True)
    assert not t.is_null()
    assert Term().is_null() and Sort().is_null()
    with pytest.raises(ValueError):
        b.assert_formula(t)
    a.reset()
    a.mk_bool(False)
    with pytest.raises(ValueError):
        a.assert_formula(t)


def test_large_presburger_constants_are_exact():
    s = Solver('QF_LIA')
    x = s.int('x')
    big = 10**90 + 123
    s.add(x == big)
    assert s.check() == Result.Sat
    assert s.model()[x] == big
    assert s.validate_model() == ModelValidation.Satisfied


def test_decimal_and_float_literals_do_not_change_value():
    s = Solver('QF_LRA')
    x = s.real('x')
    s.add(x == s.real_val('0.125'))
    assert s.check() == Result.Sat
    assert s.model()[x] == Fraction(1, 8)
    from xolver.dsl import _to_rational
    tiny = 1.0 + 2.0**-52
    assert Fraction(_to_rational(tiny)) == Fraction.from_float(tiny)
    assert Fraction(_to_rational(tiny)) != 1
    with pytest.raises((ValueError, OverflowError)):
        s.real_val('1/0')
    with pytest.raises(TypeError):
        s.int_val(1.5)


def test_models_keep_their_context_snapshot():
    s = Solver('QF_LIA')
    x = s.int('x')
    s.add(x == 42)
    assert s.check() == Result.Sat
    model = s.model()
    s.reset()
    other_x = s.int('x')
    assert model['x'] == 42
    assert model[x] == 42
    with pytest.raises(ValueError):
        model[other_x]


def test_redeclaration_is_the_same_symbol():
    s = Solver('QF_UF')
    p, q = s.bool('p'), s.bool('p')
    assert p.term == q.term
    s.add(p, ~q)
    assert s.check() == Result.Unsat
    with pytest.raises(ValueError):
        s.int('p')


def test_runtime_parameters_are_per_instance_and_change_between_queries(tmp_path):
    path = tmp_path / "quantified.smt2"
    path.write_text("(set-logic LIA)(assert (forall ((x Int)) "
                    "(exists ((y Int)) (> y x))))(check-sat)")
    a, b = RawSolver(), RawSolver()
    a.set_runtime_parameter("XOLVER_PA_WORK", "1")
    b.set_runtime_parameter("XOLVER_PA_WORK", "2000000")
    a.parse_file(str(path))
    b.parse_file(str(path))
    assert a.check_sat() == Result.Unknown
    assert b.check_sat() == Result.Sat
    a.clear_runtime_parameter("XOLVER_PA_WORK")
    assert a.check_sat() == Result.Sat
    with pytest.raises(ValueError):
        a.set_runtime_parameter("A=B", "1")
