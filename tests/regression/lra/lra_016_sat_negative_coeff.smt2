; Negative coefficient: -x >= 0 (i.e. x <= 0) is sat.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (>= (- x) 0))
(assert (>= x (- 10)))
(check-sat)
