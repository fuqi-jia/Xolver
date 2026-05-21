; VeryMax-style: positive product with linear bound — must be sat.
; Pattern: x*y > 0 with x>0, y>0, both bounded.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1)) (assert (<= x 10))
(assert (>= y 1)) (assert (<= y 10))
(assert (> (* x y) 0))
(check-sat)
