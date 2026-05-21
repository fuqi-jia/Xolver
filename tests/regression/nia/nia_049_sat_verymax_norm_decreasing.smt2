; Norm decreases: x² + y² ≥ 1 ∧ x ≥ 1 — sat (e.g. x=1, y=0).
; Watch for AlgebraicIntegerReasoner emitting GCD conflict.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 1))
(assert (>= (+ (* x x) (* y y)) 1))
(check-sat)
