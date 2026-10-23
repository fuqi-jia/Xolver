# Solver applications

Applications compose infrastructure to solve a stated problem. They do not own
shared logical foundations, SAT implementations or mathematical primitives.

| Directory | Responsibility | Current implementation |
| --- | --- | --- |
| `smt` | Satisfiability and per-logic theory composition | QF theory combinations; quantified Boolean, bit-vector, integer and real arithmetic |
| `omt` | Optimization modulo theories | `Optimize` interface; no objective search yet |
| `cp` | Constraint programming | Reserved; no algorithm yet |
| `milp` | Mixed-integer linear optimization | Reserved; no objective optimizer yet |
| `de/ode`, `de/pde` | Differential equation applications | Reserved; no algorithm yet |
| `sv/pa`, `sv/sl` | Dedicated PA and separation-logic problems | Native arithmetic and heap solvers with domain-specific models |
| `counting` | Model counting | Reserved; no algorithm yet |

`Solver.h` defines the common abstract `Solver` identity and lifetime, and
`TypedSolver<Input, Output>` supplies a virtual `solve(const Input&)`. SMT, PA,
SL and the OMT interface implement this interface. There is no default
solver that silently returns `unknown`. The different result types are deliberate:
an optimum, a count and a satisfiability decision have different meanings.

Only application entries derive from this base. `TheorySolver` is the lower-level
CDCL(T) callback contract, not an application interface; making it inherit this
base would introduce a dependency from infrastructure back to applications.

A helper used by one solver remains with that solver. Shared application-specific
code belongs to that application's `common/`, such as `smt/common/lia`. There is
no `applications/common/` and no dependency between SMT, OMT, SV or other families.
Cross-application mathematics belongs to the appropriate lower layer, after its
application-specific assumptions and input conversion have been separated.

See [the dependency and call-flow diagrams](../../docs/ARCHITECTURE.md).
