; i*r > 100 with i ∈ [0,3] ∧ r ∈ [0,3] — impossible.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const i Int) (declare-const r Real)
(assert (>= i 0)) (assert (<= i 3))
(assert (>= r 0)) (assert (<= r 3))
(assert (> (* (to_real i) r) 100))
(check-sat)
