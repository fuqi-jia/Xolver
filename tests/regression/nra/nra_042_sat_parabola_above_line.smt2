; y = x^2 + 1 always lies above y = 0 ⇒ sat with any x.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (+ (* x x) 1)))
(assert (> y 0))
(check-sat)
