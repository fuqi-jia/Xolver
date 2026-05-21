; y = x^2 + 1 never < 0.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (+ (* x x) 1)))
(assert (< y 0))
(check-sat)
