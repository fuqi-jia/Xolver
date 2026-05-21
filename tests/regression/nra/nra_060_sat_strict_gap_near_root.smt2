; Strict gap near root: x² > 0 ∧ x ≠ 0 — many witnesses; choose x = 1.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (> (* x x) 0))
(assert (distinct x 0))
(check-sat)
