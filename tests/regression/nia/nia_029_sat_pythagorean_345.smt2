; Pythagorean: x^2 + y^2 = 25 with x,y ≥ 0. Solutions include (3,4), (4,3), (5,0), (0,5).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (= (+ (* x x) (* y y)) 25))
(check-sat)
