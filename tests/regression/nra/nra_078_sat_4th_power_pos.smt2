; (x-1)^4 ≥ 0 always — even power. SAT with any x.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (>= (* (* (- x 1) (- x 1)) (* (- x 1) (- x 1))) 0))
(check-sat)
