# Xolver for Python

Python bindings for **Xolver**, a competition-grade SMT solver for quantifier-free
nonlinear arithmetic and its combinations with uninterpreted functions, arrays,
and datatypes. The design invariant is **soundness over completeness**: every
`sat` is independently re-validated and incomplete reasoning returns `unknown`
rather than risk a wrong answer.

## Install

```bash
pip install xolver
```

Linux x86_64 wheels are published with every release (GMP/MPFR are bundled, so
there is nothing else to install). macOS/Windows wheels are not built yet — on
those platforms, build from source (needs a C++20 compiler, CMake ≥ 3.16, and
`libgmp`/`libmpfr`).

## A z3-flavored API

```python
from xolver import Int, Real, And, Or, Not, solve

x, y = Int('x'), Int('y')
solve(x + y == 10, x - y == 2)          # [x = 6, y = 4]
```

Or drive a solver explicitly — note that, unlike z3, a term belongs to the
solver that created it (see *Design note* below):

```python
from xolver import Solver, sat

s = Solver('QF_NRA')
a = s.real('a')
s.add(a * a == 2, a > 0)                  # a == sqrt(2)
if s.check() == sat:
    print(s.model()[a])                   # root([1, 0, -2]) in [5/4, 3/2] ~ 1.414…

s = Solver('QF_LIA')
x, y, z = s.int('x'), s.int('y'), s.int('z')
s.add(x + y + z == 12, x < y, y < z)
print(s.check(), s.model())               # sat [x = …, y = …, z = …]
```

Model values come back as native Python types: `int`, `fractions.Fraction`,
`bool`, or an `AlgebraicNumber` (for irrational real-algebraic roots, with
`float(value)` / `.approx()` for a numeric estimate).

Supported building blocks: `Int`, `Real`, `Bool` constants; `IntVal`, `RealVal`,
`BoolVal` literals; arithmetic (`+ - * / %`, unary `-`); comparisons
(`< <= > >= == !=`); boolean `And`, `Or`, `Not`, `Implies`, `Xor`, `Ite`/`If`,
`Distinct`, and the operator forms `& | ~ ^`. Incremental solving via
`push()` / `pop()` and `check(*assumptions)`.

## The low-level binding

`xolver.RawSolver` is a faithful 1:1 wrapper of the C++ public API
(`include/xolver/`), for when you want raw `Term`/`Sort`/`Model`/`Kind` handles
or to parse SMT-LIB directly:

```python
import xolver
print(xolver.parse_smt2_string(
    "(set-logic QF_LIA)(declare-fun x () Int)(assert (> x 0))(check-sat)"))   # Result.Sat
```

## One-step control (user propagator)

Xolver exposes a CaDiCaL-style *user propagator* so you can observe and steer the
CDCL(T) search one decision at a time — watch every assignment, decision level,
and backtrack, and decide which boolean / theory atom to branch on next. Steering
is **sound by construction**: it can only change the search order, never the
verdict.

```python
import xolver
from xolver import Solver

class Trace(xolver.Propagator):
    def on_setup(self, atoms):            # observable atoms: var <-> term
        self.atoms = {a.var: a for a in atoms}
    def on_assignment(self, var, value, is_decision):
        print(("decide" if is_decision else "imply"), "var", var, "=", value)
    def on_backtrack(self, level):
        print("backtrack ->", level)
    def decide(self):
        return 0                          # 0 = let Xolver pick; or return ±var

s = Solver("QF_LIA")
x = s.int("x")
s.add(x > 0, x < 3)
s.set_propagator(Trace())
print(s.check(), s.model())               # verdict identical to no propagator
```

The propagator exposes **both levels** of the CDCL(T) loop — override only what
you need (every hook has a no-op default):

| Level | Hook | Fires when |
|-------|------|-----------|
| setup | `on_setup(atoms)` | once, with the observable atoms (`var`, `term`, `is_theory`) |
| SAT | `on_assignment(var, value, is_decision)` | a literal is assigned |
| SAT | `on_new_decision_level()` / `on_backtrack(level)` | the search branches / backjumps |
| SAT | `decide() -> int` | steer the next decision: `±var`, or `0` to defer |
| SMT | `on_fixed(var, value, atom)` | a **theory atom** is assigned a truth value |
| SMT | `on_theory_check(effort, outcome)` | the **theory consistency check** runs (`Standard`/`Full` → `Consistent`/`Conflict`/`Lemma`/`Unknown`) |
| SMT | `on_conflict(clause)` / `on_lemma(clause)` | the theory emits a conflict / lemma clause |
| SMT | `on_propagate(clause)` | the theory entails a literal |
| SMT | `on_final_check()` | a complete, theory-consistent model is found |
| gen | `generate_lemmas() -> [[±var,…]]` | **add your own** theory lemmas at the final check |

```python
import xolver
from xolver import Solver, CheckEffort, CheckOutcome

class TheoryWatch(xolver.Propagator):
    def on_fixed(self, var, value, atom):
        print("fixed atom", var, "=", value)
    def on_theory_check(self, effort, outcome):
        print("theory check", effort, "->", outcome)
    def on_conflict(self, clause):
        print("theory conflict:", clause)

s = Solver("QF_LIA")
x = s.int("x")
s.add(x > 5, x < 2)                       # infeasible -> theory conflict
s.set_propagator(TheoryWatch())
print(s.check())                          # unsat
```

`decide()` and the `on_*` hooks are **sound by construction** — observation
cannot change a verdict, and steering only reorders the search (a wrong guess is
backtracked). The single soundness-sensitive hook is `generate_lemmas()`: a
clause the current model falsifies rejects that model (the search continues),
non-excluding clauses are dropped so the search always terminates, and **you are
responsible for the validity of any lemma you add** — an invalid one can make the
verdict wrong, so it stays opt-in. See `examples/propagator_demo.py`.

## Design note — terms are solver-bound

z3 separates a `Context` (term factory) from a `Solver` (assertion stack);
Xolver fuses them, so a `Term`'s identity is tied to the `Solver` that built it.
The module-level helpers (`Int`, `Real`, `Bool`, `solve`) share one hidden
default solver; the explicit `Solver()` style keeps every term and assertion on
that one instance. Mixing terms across two different `Solver` objects raises a
clear `ValueError` instead of silently misbehaving.

## License

Apache-2.0.
