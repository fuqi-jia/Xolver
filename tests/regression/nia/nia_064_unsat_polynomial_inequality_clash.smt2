; x² < y ∧ y ≤ x ∧ x ≥ 2 — x² ≥ 4 > y, but y ≤ x ≤ x² ⇒ contradicts x² < y.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 2))
(assert (< (* x x) y))
(assert (<= y x))
(check-sat)
