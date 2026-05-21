; (x-2)^4 = -1 — even power of real is non-negative.
; Stresses degenerate discriminant + positivity.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (* (* (- x 2) (- x 2)) (* (- x 2) (- x 2))) (- 1)))
(check-sat)
