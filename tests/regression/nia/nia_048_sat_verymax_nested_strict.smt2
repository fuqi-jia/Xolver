; Nested strict bounds — VeryMax termination shape.
; (x > y) ∧ (y > z) ∧ (z ≥ 0) ∧ (x*z > 0) — sat with e.g. (3,2,1).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (> x y))
(assert (> y z))
(assert (>= z 1))
(assert (> (* x z) 0))
(check-sat)
