"""One-step user-propagator API — both SAT and SMT/theory levels.

The invariant under test is SOUNDNESS-NEUTRALITY: a propagator that only
observes and/or steers must never change the sat/unsat verdict; it may only
change the search path.
"""
import pytest

import xolver
from xolver import Solver, sat, unsat, CheckEffort, CheckOutcome


class Recorder(xolver.Propagator):
    """Records every hook at both levels."""

    def __init__(self):
        super().__init__()
        self.atoms = []
        # SAT level
        self.assignments = []
        self.levels = 0
        self.backtracks = 0
        # SMT level
        self.fixed = []
        self.checks = []
        self.conflicts = 0
        self.lemmas = 0
        self.propagations = 0
        self.final_checks = 0

    def on_setup(self, atoms):
        self.atoms = list(atoms)

    def on_assignment(self, var, value, is_decision):
        self.assignments.append((var, value, is_decision))

    def on_new_decision_level(self):
        self.levels += 1

    def on_backtrack(self, level):
        self.backtracks += 1

    def on_fixed(self, var, value, atom):
        self.fixed.append((var, value, atom.id()))

    def on_theory_check(self, effort, outcome):
        self.checks.append((effort, outcome))

    def on_conflict(self, clause):
        self.conflicts += 1

    def on_lemma(self, clause):
        self.lemmas += 1

    def on_propagate(self, clause):
        self.propagations += 1

    def on_final_check(self):
        self.final_checks += 1


# --- SAT-level observation ---------------------------------------------------
def test_observer_preserves_verdict_sat():
    s = Solver("QF_LIA")
    x, y = s.int("x"), s.int("y")
    s.add(x + y == 4, x > 0, y > 0)
    rec = Recorder()
    s.set_propagator(rec)
    assert s.check() == sat
    assert len(rec.atoms) >= 1          # onSetup delivered the observable atoms
    assert len(rec.assignments) >= 1    # saw SAT-level assignments


def test_observer_preserves_verdict_unsat():
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0, x < 0)
    rec = Recorder()
    s.set_propagator(rec)
    assert s.check() == unsat


def test_observed_atom_fields():
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0)
    rec = Recorder()
    s.set_propagator(rec)
    s.check()
    for a in rec.atoms:
        assert isinstance(a.var, int) and a.var >= 1
        assert hasattr(a, "term")
        assert isinstance(a.is_theory, bool)


# --- SMT/theory-level observation --------------------------------------------
def test_smt_sat_runs_consistent_final_check():
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0, x < 10)
    rec = Recorder()
    s.set_propagator(rec)
    assert s.check() == sat
    # a theory atom was fixed, and a Full-effort Consistent check confirmed sat
    assert len(rec.fixed) >= 1
    assert rec.final_checks >= 1
    assert any(e == CheckEffort.Full and o == CheckOutcome.Consistent
               for e, o in rec.checks)


def test_smt_unsat_exposes_theory_conflict():
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 5, x < 2)
    rec = Recorder()
    s.set_propagator(rec)
    assert s.check() == unsat
    # the theory check surfaced a Conflict (the lemma/conflict was exposed)
    assert rec.conflicts >= 1
    assert any(o == CheckOutcome.Conflict for _, o in rec.checks)


def test_smt_nra_consistent():
    s = Solver("QF_NRA")
    a = s.real("a")
    s.add(a * a == 2, a > 0)
    rec = Recorder()
    s.set_propagator(rec)
    assert s.check() == sat
    assert rec.final_checks >= 1


# --- decision steering (must not crash, must preserve verdict) ----------------
def test_steering_preserves_verdict():
    def solve(use_prop):
        s = Solver("QF_LIA")
        x = s.int("x")
        atom = x > 5
        s.add(atom, x < 10)
        if use_prop:
            class PreferTrue(xolver.Propagator):
                def __init__(self, tid):
                    super().__init__()
                    self._tid, self._lit = tid, 0
                def on_setup(self, atoms):
                    for a in atoms:
                        if a.term.id() == self._tid:
                            self._lit = a.var
                def decide(self):
                    lit, self._lit = self._lit, 0
                    return lit
            s.set_propagator(PreferTrue(atom.term.id()))
        return s.check()

    assert solve(False) == solve(True) == sat


# --- lemma generation (advanced) ---------------------------------------------
def test_generate_lemmas_noop_preserves_verdict():
    # Returning no lemmas (the default) must be a no-op.
    class NoLemmas(xolver.Propagator):
        def generate_lemmas(self):
            return []
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 0, x < 5)
    s.set_propagator(NoLemmas())
    assert s.check() == sat
