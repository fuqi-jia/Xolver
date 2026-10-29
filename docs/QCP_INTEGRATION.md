# QCP SMT integration

`tools/integration/qcp_backend.py` discharges pending Rocq verification
conditions using a selectable Xolver or Z3 binary. The pinned QCP symbolic
executor remains common to both backends; its internal SMT calls are opaque.

## Supported conditions

The typed adapter accepts explicit `Z` and `bool` binders, integer arithmetic,
comparisons, Boolean connectives, signed remainder and division, and `Zgcd` /
`Z.gcd`. Division and remainder preserve Rocq's signed and zero-divisor semantics.
Owned signed `Int` cells contribute range facts only after recognizing the entire
positive assertion tree.

GCD uses a shared uninterpreted function with valid, finite ground instances of
nonnegativity, zero boundaries, symmetry and the Euclidean remainder identity.
There is no bounded enumeration of a guessed GCD. Missing instances may prevent
discharge; SAT on this abstraction does not refute the program.

Named goal definitions and closed conjunctions, disjunctions and implications
can be expanded into sufficient obligations. Conjunction requires both children;
disjunction currently attempts the left child; implication attempts its
consequent without assuming the antecedent. These stronger conditions may fail
on otherwise provable VCs. Query manifests record the selected proof path and
every additional integer-function fact.

## Execution and evidence

Run under a single ExperimentOS CPU lease on Panda1:

```bash
python3 tools/integration/qcp_backend.py --goals CASE_goal.v \
  --manual CASE_proof_manual.v --assigned CONDITION --backend xolver \
  --binary FROZEN_XOLVER --timeout 60 --output NEW_DIRECTORY
```

Each query has a 60-second maximum wall budget and 16 GiB memory limit. Inputs,
adapter and frozen executable are hashed. UNSAT emits an unchecked proof
candidate, using the same Rocq reconstruction for both backends. Follow QCP's
`verification-orchestrator` controller through group, parent and canonical
final checks. A query answer or candidate alone never verifies a C program.
`audit_qcp_program.py` audits complete witnesses and authentic controller results;
its query-time sum is not an end-to-end performance measurement.
