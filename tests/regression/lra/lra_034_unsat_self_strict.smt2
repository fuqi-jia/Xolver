; x < x is always false.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< x x))
(check-sat)
