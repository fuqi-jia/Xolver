; Strict vs non-strict at the same point: x < 1 and x >= 1.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< x 1))
(assert (>= x 1))
(check-sat)
