; 0 = 1 after zeroing coefficients.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (+ (* 0 x) 0) 1))
(check-sat)
