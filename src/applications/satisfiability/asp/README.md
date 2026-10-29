# Finite answer-set programming

`Solver::solve(Problem)` accepts a finite ground program: normal rules,
independent choice heads, nonnegative weighted rule bodies, assumptions, output
conditions and signed integer objectives. Higher optimization priorities precede
lower ones. The default injected SAT factory uses Xolver's existing backend.

```cpp
#include "applications/satisfiability/asp/Solver.h"
using namespace xolver::applications::satisfiability::asp;
Problem problem;
problem.program.rules = {{true, {1, 2}, false, 0, {}}}; // {a;b}.
problem.program.objectives = {{0, {{1, -3}, {2, 2}}}};
auto answer = Solver().solve(problem); // optimum: a=true, b=false, cost=-3
```

ASP adds stable-model semantics to ordinary Boolean feasibility. Completion
provides candidates; an independent reduct worklist computes their least models.
Unsupported positive cycles produce weighted unfounded-set constraints. A SAT
result requires the original rules and the reduct to validate. Every optimality
claim additionally requires all higher-priority objectives to be fixed exactly.

`search/optimization/BooleanOptimizer` supplies reusable lexicographic integer
optimization through feasibility and retained-witness callbacks. It uses the
shared bit-blast/PB encoders. Existing MaxSMT's exact rational-weight API remains
separate; integer scaling is a caller's explicit responsibility.

`Unknown` may carry a checked incumbent, never an optimum. Limits bound formula
work, SAT calls, variables, deadline and cooperative cancellation. Disjunctive
multi-atom heads, incremental ASPIF steps and unsupported semantic directives
return `Unsupported`; they do not fall back to ordinary SAT.

## CLI and grounding

Build target `xolver-asp` reads single-step ASPIF 1.0 and emits Clingo-style JSON:

```sh
clingo --mode=gringo --output=intermediate input.lp | build/bin/xolver-asp
build/bin/xolver-asp --timeout-ms 60000 input.aspif
```

The first command is a parser/grounder only. Xolver performs stable-model search
and optimization. The native CLI itself has no Clingo dependency. Output includes
exact integer costs and complete atom identities for independent witness replay.
Projection directives preserve existence and optimization; this API returns one
witness and does not enumerate projected answer sets.

## Original Draco integration

[DracoBackend](../../../../tools/integration/draco_backend.py) replaces the
original `draco.run.run_clingo` seam while keeping Draco's `run`, `Result` and
`is_valid` code. Source [uwdata/draco](https://github.com/uwdata/draco) is pinned to
`607e9134b3749210fe13b33248bf139a22d7b787`; rules, weights and examples are hashed in
[the source manifest](../../../../tools/integration/draco-source.json).

Grounding and solving have separate commands, roles, hashes and timing receipts.
Source objective tuples are deduplicated by the grounder; ASPIF terms remain
additive. Ignored/non-integer objective tuples, including `#inf`, are rejected
explicitly. An incomplete Xolver result raises an exception so Draco cannot
mistake it for `None`/UNSAT. The context manager changes module bindings; use
separate processes for concurrent adapters.

Independent tests compare reduct subset-minimality, exact signed objective
vectors, full Clingo verdicts and complete internal-model replay. The development
integration uses original ASP query facts and Draco's result parser. Draco 2 and
the separate JavaScript Vega-Lite conversion are outside this initial adapter.
No performance-superiority claim follows from these functional checks.
