; x^2 + y - 4 ≥ 0 — sat with e.g. (2,0), (0,4).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0)) (assert (<= x 5))
(assert (>= y 0)) (assert (<= y 10))
(assert (>= (- (+ (* x x) y) 4) 0))
(check-sat)
