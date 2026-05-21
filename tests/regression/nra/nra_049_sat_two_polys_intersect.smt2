; y = x^2, y = 2x — intersect at x=0, x=2.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* x x)))
(assert (= y (* 2 x)))
(check-sat)
