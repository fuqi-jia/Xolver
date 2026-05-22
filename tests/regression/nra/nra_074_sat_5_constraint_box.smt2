; Box + 1 nonlinear: 0 ≤ x ≤ 1, 0 ≤ y ≤ 1, x² + y ≥ 1/2. SAT.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0)) (assert (<= x 1))
(assert (>= y 0)) (assert (<= y 1))
(assert (>= (+ (* x x) y) (/ 1 2)))
(check-sat)
