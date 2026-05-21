; Minimal LIA false-sat repro target: negated linear atom.
; (not (>= x 5)) AND x >= 5 — must be unsat.
; If Atomizer treats (not …) lazily, solver may miss the negation.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (not (>= x 5)))
(assert (>= x 5))
(check-sat)
