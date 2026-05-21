; Two equations with parallel hyperplanes (same LHS, different RHS) are unsat.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* 2 x) (* 3 y)) 5))
(assert (= (+ (* 2 x) (* 3 y)) 6))
(check-sat)
