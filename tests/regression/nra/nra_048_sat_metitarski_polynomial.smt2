; Meti-tarski style: high-degree polynomial inequality with small witness.
; x ∈ [0.5, 1.5] and x^4 - 2x^2 + 1 ≤ 1 — sat (witness x=1).
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (>= x (/ 1 2)))
(assert (<= x (/ 3 2)))
(assert (<= (- (+ (* (* x x) (* x x)) 1) (* 2 (* x x))) 1))
(check-sat)
