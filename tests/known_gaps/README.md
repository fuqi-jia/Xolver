# Known gaps (checked by CTest)

Oracle-verified (z3 + cvc5) SMT-LIB cases that xolver does **not yet solve** but
must never answer *wrong* on. CTest's `known-gaps` entry permits `unknown`, but
an opposite verdict, a crash, or a timeout fails. Move a case into
`tests/regression/<logic>/` when it must also meet the completeness requirement.

These are *completeness* gaps (xolver returns `unknown`), never soundness bugs —
a wrong verdict is checked on every test run, without waiting for promotion.

## nra/ — multivariate real feasibility

- `box_sector_joint_reasons.smt2` has a rational witness recorded in the input
  and independently checked by Z3 and cvc5. Exact covering does not currently
  establish feasibility for this system. `unknown` is allowed; `unsat`
  contradicts the witness. The unit suite also checks this obligation directly.

## ufdtnia/ — QF_UFDTNIA finite-datatype cardinality (one remaining)

- `ufdtnia_004_sat_tester.smt2` — `((_ is red) c) ∧ x*x=25`. SAT (c=red, x=5),
  z3/cvc5 <50 ms. xolver `unknown` because of the **finite-DT N-O floor**
  (`DtReasoner::modelFullyDetermined`: a finite — non-stably-infinite — datatype
  in combination is conservatively floored to avoid a cardinality/pigeonhole
  false-SAT). For a single determined `c` there is no cardinality risk, but a
  *sound* relaxation needs real N-O finite-sort cardinality reasoning (count
  pairwise-distinct finite-DT terms vs the sort's value count) plus a Tester
  case in ArithModelValidator. Soundness-sensitive; deferred. Do NOT just delete
  the floor — that reintroduces finite-enum pigeonhole false-SATs.

RESOLVED (promoted to `tests/regression/ufdtnia/`):
- `ufdtnia_005` (tester clash wrongly SAT) — Atomizer now routes EUF-owned bool
  predicates (UFApply/Tester/Select) to EUF in combination + DtReasoner
  tester-vs-tester clash check.
- `ufdtnia_001` (selector field `x*x=16`) and `ufdtnia_006` (UF over a datatype
  value) — DT+NIA model construction: the Purifier's selector/UF bridges
  (`(= v (fst p))`, `(= u (f p))`) now back-fill the model validator
  (ArithModelValidator selector/UFApply ExprId override), mirroring the array-read
  bridge back-fill, so the genuine sat is confirmed instead of floored.
