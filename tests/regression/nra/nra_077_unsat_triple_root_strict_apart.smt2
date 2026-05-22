; (x-2)^3 = 0 ∧ x > 3 — unsat (only x=2 satisfies the cube).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (* (- x 2) (* (- x 2) (- x 2))) 0))
(assert (> x 3))
(check-sat)
