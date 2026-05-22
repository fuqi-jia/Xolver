; Mix x² and x*y to force both Square cut and McCormick generator.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0)) (assert (<= x 3))
(assert (>= y 0)) (assert (<= y 3))
(assert (>= (+ (* x x) (* x y)) 1))
(check-sat)
