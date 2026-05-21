; Multi-variable polynomial inspired by atan chain: |x| ≤ 1 ∧ |y| ≤ 1 ∧
; |x - y - (x*y*(x-y))| ≤ some bound — sat with (x=y=0).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (<= x 1)) (assert (>= x (- 1)))
(assert (<= y 1)) (assert (>= y (- 1)))
(assert (<= (- x y) (/ 1 10)))
(assert (>= (- x y) (- (/ 1 10))))
(check-sat)
