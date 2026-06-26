"""One-step control via a CaDiCaL-style user propagator.

Two demos:
  1. TraceProp  — OBSERVE the CDCL(T) search: every decision, propagation,
                  new level, and backtrack.
  2. PreferTrue — STEER the search: force a chosen boolean/theory atom to be
                  the next decision, at its True phase.

Steering is sound by construction — a wrong guess is just backtracked — so the
verdict is identical with or without the propagator; only the search path
changes. Run:  python python/examples/propagator_demo.py
"""
import xolver
from xolver import Solver


class TraceProp(xolver.Propagator):
    """Print the search as it unfolds (the 'one step' view)."""

    def __init__(self):
        super().__init__()
        self.atoms = {}          # var -> ObservedAtom
        self.decisions = 0

    def on_setup(self, atoms):
        for a in atoms:
            self.atoms[a.var] = a
        print(f"[setup] {len(atoms)} observable atoms")

    def on_assignment(self, var, value, is_decision):
        tag = "DECIDE   " if is_decision else "propagate"
        kind = "theory" if (var in self.atoms and self.atoms[var].is_theory) else "bool"
        if is_decision:
            self.decisions += 1
        print(f"  [{tag}] {kind} var {var} = {value}")

    def on_new_decision_level(self):
        print("  [level +1]")

    def on_backtrack(self, level):
        print(f"  [backtrack -> level {level}]")


class PreferTrue(xolver.Propagator):
    """Decide a specific atom (given as an ExprRef) True, first."""

    def __init__(self, target):
        super().__init__()
        self._target_id = target.term.id()
        self._lit = 0

    def on_setup(self, atoms):
        for a in atoms:
            if a.term.id() == self._target_id:
                self._lit = a.var           # positive var => True phase
                print(f"[steer] will decide atom var {a.var} = True first")

    def decide(self):
        lit, self._lit = self._lit, 0       # fire once, then defer to Xolver
        return lit


def demo_trace():
    print("== trace the search ==")
    s = Solver("QF_LIA")
    x, y = s.int("x"), s.int("y")
    s.add(x + y == 4, x > 0, y > 0)
    p = TraceProp()
    s.set_propagator(p)
    print("verdict:", s.check())
    print("model:", s.model())
    print(f"(observed {p.decisions} decisions)")


def demo_steer():
    print("\n== steer a decision ==")
    s = Solver("QF_LIA")
    x = s.int("x")
    atom = x > 5
    s.add(atom, x < 10)                 # x in (5, 10)
    s.set_propagator(PreferTrue(atom))
    print("verdict:", s.check())        # sat, identical to no-propagator
    print("model:", s.model())


class TheoryWatch(xolver.Propagator):
    """Watch the SMT/theory-level step: atoms being fixed, the theory
    consistency check (effort + outcome), and the conflicts / lemmas it emits."""

    def __init__(self):
        super().__init__()
        self.checks = []

    def on_fixed(self, var, value, atom):
        print(f"  [fixed] theory atom var {var} = {value} (term {atom.id()})")

    def on_theory_check(self, effort, outcome):
        self.checks.append((effort, outcome))
        print(f"  [theory-check] {effort} -> {outcome}")

    def on_conflict(self, clause):
        print(f"  [conflict] clause = {clause}")

    def on_lemma(self, clause):
        print(f"  [lemma] clause = {clause}")

    def on_final_check(self):
        print("  [final-check] complete theory-consistent model")


def demo_theory():
    print("\n== watch the SMT/theory step (unsat) ==")
    s = Solver("QF_LIA")
    x = s.int("x")
    s.add(x > 5, x < 2)                  # infeasible -> theory conflict
    s.set_propagator(TheoryWatch())
    print("verdict:", s.check())


if __name__ == "__main__":
    demo_trace()
    demo_steer()
    demo_theory()
