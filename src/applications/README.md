# Solver applications

The top-level categories are `satisfiability`, `optimization`, `counting`,
`verification` and `dynamics` (ODE/PDE). Solver kinds live beneath their category;
there are no forwarding headers at retired paths.

Applications compose infrastructure through `Solver` and `TypedSolver<Input,
Output>`. Problem contracts describe the application's mathematical semantics;
backend support does not restrict the shape of these contracts.

| Application | Problem and result | Executable backend |
| --- | --- | --- |
| `satisfiability/sat` | DIMACS clauses and assumptions; checked assignments or failed assumptions | Injectable SAT backend, sparse variable mapping |
| `satisfiability/smt` | Native assertions; sat/unsat/unknown and models | Arithmetic, UF, arrays, datatypes, finite BV combinations, FP predicates/concrete arithmetic and strings |
| `optimization/omt` | Native objectives, priorities and exact objective values | Lexicographic Bool/BV and linear arithmetic optimization |
| `optimization/maxsat` | Hard clauses and exact rational weighted soft clauses | Shared MaxSMT optimization engine |
| `optimization/maxsmt` | Hard formulas, rational weighted soft formulas, optimum/incumbent bounds | Exact bounded truth-pattern search with an injected theory backend |
| `counting` | Native assertions and an explicit projected tuple | Exact Bool/BV and linear integer projection; infinite-domain detection |
| `optimization/cp` | Native constraints, variable domains and global constraints | Domains, all-different, tables, element and cardinality constraints |
| `optimization/milp` | Rational linear constraints, integer/continuous variables, bounds and objective | Exact rational simplex and integer branch and bound |
| `verification/model_checking` | Conditions and transition systems | Symbolic reachable-region synthesis, candidate invariants, k-induction and certificate replay |
| `verification/pa`, `verification/sl` | Presburger or explicit heap semantics | Integer elimination, heap entailments and simultaneous predicate induction |
| `dynamics/ode`, `dynamics/pde` | Native equations, coordinates, parameters and derivative applications | Parametric polynomial solution search with exact substitution checks |

The [MaxSMT API](optimization/maxsmt/README.md) uses the same injected decision contract without
a dependency on the SMT or OMT application. The independent
[parallel API](../parallel/README.md) supplies typed tasks and explicit worker
widths; application clients can compose these interfaces.

The CLI's SMT session supplies the stateful ground callback. The application
headers also support direct C++ use; CP and verification-condition clients inject
`DecisionOracle`. Dependencies stay within one category; cross-category composition uses
injected contracts. MaxSAT and MaxSMT share the optimization engine. No language frontend is inferred for SV.

An optimization optimum, a projected count and a differential solution have
different result types. A bounded search failure cannot imply nonexistence.
Unknown results carry a reason; any incumbent retained after resource exhaustion
is not an optimality claim. Resource controls bound work, not input semantics.

Helpers used only by one backend stay with it. SMT's finite-combination code is
in `satisfiability/smt/common/finite`; native DAG construction is in `ir/NativeBuilder.h`, and
exact rectangular linear solving is in `algebra/linear`. Shared mathematics and
formula representations do not belong in an `applications/common` folder.

See [architecture and query flow](../../docs/ARCHITECTURE.md) and the README in
each application for capability and evidence limits.

[Executable C++ examples](../../tests/unit/test_application_prototypes.cpp) cover
all application families, including projected counts, lexicographic objectives,
mixed integer/continuous constraints, verification conditions and initial/boundary
data for differential equations. Run them with:

```sh
./build/tests/xolver_unit_tests --test-case='application prototypes:*'
```

The [application algorithm tests](../../tests/unit/test_application_foundations.cpp)
exercise exact optimization, independent mixed-integer reference enumeration,
open bounds, projected integer counts, CP constraints, inductive invariants and
parametric differential equations:

```sh
./build/tests/xolver_unit_tests --test-case='application foundations:*'
```

The [SMT theory examples](../../tests/unit/test_theory_applications.cpp) and
[external model validation](../../tools/fuzz/fuzz_theory_applications.py) exercise
native parsing, theory combinations and serialized interpretations.
