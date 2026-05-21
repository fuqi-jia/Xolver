; x^2 = 4 has real solutions x = ±2.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* x x) 4))
(check-sat)
