; Brown 2001-style: dimension-3 polynomial with non-trivial cylindrical decomposition.
; Relaxed to be satisfiable for testing.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (>= (- (+ (* x x) (* y y) (* z z)) (* 2 (* x y z))) 0))
(assert (<= x 1)) (assert (>= x (- 1)))
(assert (<= y 1)) (assert (>= y (- 1)))
(assert (<= z 1)) (assert (>= z (- 1)))
(check-sat)
