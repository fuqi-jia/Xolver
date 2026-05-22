; Quadratic + linear in 2 vars — sector lifting after eliminating y via linear.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))
(assert (= (+ x y) 1))
(check-sat)
