; Meti-tarski-shape 2-var polynomial inequality with witness.
; x² + y² ≤ 4 ∧ x + y ≥ 1 — sat with (x=1, y=1).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) 4))
(assert (>= (+ x y) 1))
(check-sat)
