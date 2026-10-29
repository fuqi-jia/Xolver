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
optimization through feasibility and atomic incumbent-publication callbacks. It uses the
shared bit-blast/PB encoders. Existing MaxSMT's exact rational-weight API remains
separate; integer scaling is a caller's explicit responsibility.

`SolveMode::Feasible` skips optimization; its costs evaluate the retained model.
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

## Latest Draco 2 integration

[DracoBackend](../../../../tools/integration/draco_backend.py) injects an explicit
runner into individual instances of the current `Draco` class. It reuses the
original method code, defaults and closures with private runner bindings;
module globals and other backend instances remain unchanged. It returns the
current `Model(answer_set, cost, number)` objects and supports `check_spec`,
`complete_spec`, `count_preferences`, `get_violations` and the raw runner.

```python
import draco
import importlib
from pathlib import Path
from draco_backend import DracoBackend, SubprocessGrounder
backend = DracoBackend(importlib.import_module("draco.run"),
                       Path("build/bin/xolver-asp"), SubprocessGrounder(("clingo",)))
instance = backend.bind(draco.Draco())
models = list(instance.complete_spec(query_facts, models=2))
```

[cmudig/draco2](https://github.com/cmudig/draco2) main is frozen at
`580047a9b5a41b153b24059275e8050b36c38658` (version 2.0.1, observed 2026-10-29).
Rules, weights, API code and public examples are hashed in
[the source manifest](../../../../tools/integration/draco-source.json).
There is no result cache. Every native invocation records backend identity,
source/ASPIF/binary hashes, arguments and separate grounding/solving timings.

Top-K blocks complete internal ASP models and proves each remaining optimum;
models at the same cost may differ from another solver's tie order. Non-top-K
optimization emits one proven optimum without intermediate search incumbents.
Without objectives, or when top-K with unlimited models explicitly ignores
objectives, finite model generation continues until exhaustion or the budget.
Non-top-K projection suppresses repeated shown models and honors `#project`.

Source objective tuples are deduplicated by the grounder; ASPIF terms remain
additive. Non-integer/ignored objective tuples such as `#inf` and unsupported
foreign solver options raise explicit errors. Incomplete solves raise an
exception rather than becoming an empty model generator. The production adapter
never invokes `clingo.Control.solve`; Clingo symbols and ASTs serve as parsers.

Independent checks cover reduct subset-minimality, signed objective vectors,
full internal-model replay, original Draco 2 methods and isolated concurrent
backend instances. Visualization rendering and FastAPI routing are separate
clients. These initial functional checks make no performance-superiority claim.
