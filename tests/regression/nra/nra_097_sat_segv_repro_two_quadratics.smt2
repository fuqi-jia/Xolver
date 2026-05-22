; Two bivariate quadratics — most generic shape for sector lifting bug.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 4))
(assert (= (- (* x x) (* y y)) 0))
(check-sat)
