; Hyperbola xy = 1. Sat with (1,1), (2, 0.5), etc.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (* x y) 1))
(check-sat)
