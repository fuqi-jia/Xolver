; Parabola y = x² ∩ circle x² + y² = 2. Substitute: y + y² = 2 ⇒ y=1 or y=-2.
; y must be ≥ 0 from y=x², so y=1, x = ±1. SAT.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* x x)))
(assert (= (+ (* x x) (* y y)) 2))
(check-sat)
