; x^2 + y^2 = 1 AND y = x — two solutions ±√2/2. Bivariate CDCAC.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= y x))
(check-sat)
