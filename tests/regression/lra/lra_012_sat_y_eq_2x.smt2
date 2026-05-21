; Functional dependency y = 2x + bounds.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* 2 x)))
(assert (> x 0))
(assert (< y 10))
(check-sat)
