; ¬(x ≤ 1) ⇔ x > 1; combined with x < 1 unsat.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (not (<= x 1)))
(assert (< x 1))
(check-sat)
