; Classic Bland cycling avoidance test: many equal-coefficient rows.
; Without Bland's rule a naive simplex may cycle. Should solve fast.

(set-info :status sat)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const w Real)
(assert (>= x 0)) (assert (>= y 0)) (assert (>= z 0)) (assert (>= w 0))
(assert (<= (+ x y z w) 4))
(assert (= (+ x y) (+ z w)))
(assert (= (+ x z) (+ y w)))
(check-sat)
