# QCP SMT integration

`tools/integration/qcp_native_backend.py` wraps the pinned QCP executable and
routes its actual SAT-entry calls through a hash-checked execution guard and
preload library. QCP performs parsing and symbolic execution; the adapter
translates the captured formulas for a frozen Xolver worker or Z3 process.
Each occurrence has a fresh SMT context, including repeated formulas. Native
records bind the executable, bridge, solver, formula and query bytes.

`tools/integration/qcp_backend.py` also discharges typed pending Rocq conditions
using a selected backend. Its supported conditions and sufficient-obligation
translation are described below. A complete native workflow still follows the
QCP controller through final symexec replay and Rocq checks.

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

## Program coverage and timing

Count verified function bodies separately from function contracts. The original
`gcd.c` contains one body (`gcd`) and an external `abs` declaration whose contract
is assumed. The original `max3` postcondition guarantees an upper bound of all
three inputs; it does not state membership in the inputs. Verification results
refer to these frozen properties.

Count actual native SMT occurrences across the full workflow when reporting a
workflow total. The older R1142 total of780 covers final-check sessions only;
the controlled branch workflow R1231 performs564 calls per backend across three
symexec sessions. Bridge-only receipts do not certify the program. Completed
controller state, original-source hashes and full Rocq checks provide that link.
Report executed-stage time and orchestration wall time separately; a single pair
with different initial library policies does not establish end-to-end speedup.
