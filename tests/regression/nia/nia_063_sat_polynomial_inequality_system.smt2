; x² ≥ y ∧ y ≥ x ∧ 0 ≤ x ≤ 5 — sat with x=2, y=2.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0)) (assert (<= x 5))
(assert (>= (* x x) y))
(assert (>= y x))
(check-sat)
