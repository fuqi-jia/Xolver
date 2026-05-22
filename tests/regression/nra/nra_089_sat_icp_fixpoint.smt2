; ICP must reach fixpoint: x = y² ∧ y = x² ⇒ x⁴ = x ⇒ x ∈ {0, 1}.
; Single witness exists.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= x (* y y)))
(assert (= y (* x x)))
(check-sat)
