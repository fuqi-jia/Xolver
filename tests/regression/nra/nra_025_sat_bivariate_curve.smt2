; Bivariate curve y = x^2 + 1, ask any point on it.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (+ (* x x) 1)))
(assert (>= x (- 10)))
(assert (<= x 10))
(check-sat)
