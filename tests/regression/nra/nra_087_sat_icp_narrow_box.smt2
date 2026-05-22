; Narrow box: x ∈ [0.999, 1.001], y ∈ [0.999, 1.001], x*y ∈ [0.99, 1.01].
; Should iteratively contract.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x (/ 999 1000))) (assert (<= x (/ 1001 1000)))
(assert (>= y (/ 999 1000))) (assert (<= y (/ 1001 1000)))
(assert (>= (* x y) (/ 99 100)))
(assert (<= (* x y) (/ 101 100)))
(check-sat)
