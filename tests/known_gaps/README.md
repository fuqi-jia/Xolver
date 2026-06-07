# Known gaps (not run by CTest)

Oracle-verified (z3 + cvc5) SMT-LIB cases that xolver does **not yet solve** but
must never answer *wrong* on. They are kept here as documentation + future
regression seeds. They are **not** registered in `tests/CMakeLists.txt`, so the
green regression suite stays green; move a case into `tests/regression/<logic>/`
the day xolver solves it.

These are *completeness* gaps (xolver returns `unknown`), never soundness bugs —
a wrong verdict would still be caught if one of these is ever promoted.

## ufdtnia/ — QF_UFDTNIA SAT cases needing combination model construction

All three are SAT (z3/cvc5 in <50 ms) but xolver returns `unknown`: the
combination layer (EUF/DT + NIA) does not construct/accept a joint model over
datatype fields + nonlinear integers. Same class as the QF_ANIA array-combination
model-acceptance gap (see memory `project_nia_linear_decide` /
`project_array_sat_model_construction`).

- `ufdtnia_001_sat_selector_nonlinear.smt2` — selector field with `x*x=16`.
- `ufdtnia_004_sat_tester.smt2` — decided tester + `x*x=25`.
- `ufdtnia_006_sat_uf_over_datatype.smt2` — UF over a datatype value + product.

Note: the *soundness* sibling of this cluster — `ufdtnia_005` (tester clash
wrongly SAT in combination) — was a real bug, now FIXED (Atomizer routes
EUF-owned bool predicates to EUF in combination; DtReasoner gained a direct
tester-vs-tester clash check) and promoted to `tests/regression/ufdtnia/`.
