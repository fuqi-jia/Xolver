; McCormick over crossing-zero bounds: x ∈ [-2, 1], y ∈ [-1, 2].
; x*y ∈ [-2, 4]. Asserting x*y = 0 — sat (e.g. x=0).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x (- 2))) (assert (<= x 1))
(assert (>= y (- 1))) (assert (<= y 2))
(assert (= (* x y) 0))
(check-sat)
