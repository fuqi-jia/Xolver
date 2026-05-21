; Rational coefficients: (1/2) x + (1/3) y = 1 with x,y free.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* (/ 1 2) x) (* (/ 1 3) y)) 1))
(check-sat)
