; Perfect square (x-1)^2 = 0 has double root at x = 1.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (- x 1) (- x 1)) 0))
(check-sat)
