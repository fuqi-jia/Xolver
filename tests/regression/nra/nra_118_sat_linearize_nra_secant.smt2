; Square cut secant: x ∈ [0, 4], x² ≤ 4x ⇒ x ≤ 4 (always in box). SAT.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (>= x 0)) (assert (<= x 4))
(assert (<= (* x x) (* 4 x)))
(check-sat)
