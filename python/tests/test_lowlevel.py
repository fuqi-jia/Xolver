"""Low-level binding: 1:1 wrapper over the C++ public API."""
import xolver
from xolver import RawSolver, Result, Kind


def test_version_string():
    assert isinstance(xolver.__version__, str)
    assert xolver.__version__.count(".") >= 1


def test_parse_smt2_string_sat():
    r = xolver.parse_smt2_string(
        "(set-logic QF_LIA)(declare-fun x () Int)(assert (> x 0))(check-sat)")
    assert r == Result.Sat


def test_parse_smt2_string_unsat():
    r = xolver.parse_smt2_string(
        "(set-logic QF_LIA)(declare-fun x () Int)"
        "(assert (> x 0))(assert (< x 0))(check-sat)")
    assert r == Result.Unsat


def test_programmatic_terms_sat():
    s = RawSolver()
    s.set_logic("QF_LIA")
    ints = s.int_sort()
    x = s.mk_const(ints, "x")
    zero = s.mk_int(0)
    s.assert_formula(s.mk_op(Kind.Gt, [x, zero]))
    assert s.check_sat() == Result.Sat


def test_programmatic_terms_unsat():
    s = RawSolver()
    s.set_logic("QF_LIA")
    ints = s.int_sort()
    x = s.mk_const(ints, "x")
    zero = s.mk_int(0)
    s.assert_formula(s.mk_op(Kind.Gt, [x, zero]))
    s.assert_formula(s.mk_op(Kind.Lt, [x, zero]))
    assert s.check_sat() == Result.Unsat


def test_result_to_string():
    assert xolver.result_to_string(Result.Sat) == "sat"
    assert xolver.result_to_string(Result.Unsat) == "unsat"
    assert xolver.result_to_string(Result.Unknown) == "unknown"
