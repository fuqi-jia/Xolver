; NRA McCormick: x*y bound in unit box.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0)) (assert (<= x 1))
(assert (>= y 0)) (assert (<= y 1))
(assert (>= (* x y) (/ 1 4)))
(check-sat)
