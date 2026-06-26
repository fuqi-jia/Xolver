"""Xolver — a competition-grade SMT solver for nonlinear arithmetic and its
combinations with UF, arrays, and datatypes.

Two layers are exposed:

* a **z3-flavored Pythonic API** (the headline): ``Solver``, ``Int``, ``Real``,
  ``Bool``, ``And``/``Or``/``Not``/``Implies``/``Ite``, ``solve`` — build
  formulas with Python operators; and
* the **low-level binding** under :data:`RawSolver` / :mod:`xolver._xolver`
  (``Term``, ``Sort``, ``Model``, ``Kind`` …) — a faithful 1:1 wrapper over the
  C++ public API, for when you need the raw handles.

Quick start::

    from xolver import Int, solve
    x, y = Int('x'), Int('y')
    solve(x + y == 10, x - y == 2)          # [x = 6, y = 4]

    from xolver import Solver
    s = Solver('QF_NRA')
    a = s.real('a')
    s.add(a * a == 2, a > 0)
    print(s.check(), s.model())
"""

from __future__ import annotations

import os
import tempfile

# The compiled extension (low-level handles).
from . import _xolver
from ._xolver import (  # noqa: F401
    Term,
    Sort,
    Model,
    Kind,
    Result,
    Propagator,
    ObservedAtom,
    CheckEffort,
    CheckOutcome,
    result_to_string,
    set_verbose,
    get_verbose,
    __version__,
)

# The low-level solver, kept available under an unambiguous name.
RawSolver = _xolver.Solver

# The z3-flavored Pythonic API is the headline surface.
from .dsl import (  # noqa: F401,E402
    Solver,
    ExprRef,
    ModelRef,
    Int, Real, Bool,
    IntVal, RealVal, BoolVal,
    And, Or, Not, Implies, Xor, Ite, If, Distinct,
    solve, sat, unsat, unknown,
)

__all__ = [
    # Pythonic API
    "Solver", "ExprRef", "ModelRef",
    "Int", "Real", "Bool", "IntVal", "RealVal", "BoolVal",
    "And", "Or", "Not", "Implies", "Xor", "Ite", "If", "Distinct",
    "solve", "sat", "unsat", "unknown",
    # Low-level
    "RawSolver", "Term", "Sort", "Model", "Kind", "Result", "result_to_string",
    # One-step control
    "Propagator", "ObservedAtom", "CheckEffort", "CheckOutcome",
    # Helpers
    "parse_smt2_string", "set_verbose", "get_verbose", "__version__",
]


def parse_smt2_string(text: str) -> Result:
    """Parse an SMT-LIB 2 *string* and run its ``(check-sat)``.

    The C++ API only parses files, so this writes ``text`` to a temporary file
    and calls the low-level ``parse_file``. Returns the :class:`Result`.
    """
    s = RawSolver()
    fd, path = tempfile.mkstemp(suffix=".smt2", text=True)
    try:
        with os.fdopen(fd, "w") as fh:
            fh.write(text)
        if not s.parse_file(path):
            raise ValueError("failed to parse SMT-LIB 2 input")
        return s.check_sat()
    finally:
        os.unlink(path)
