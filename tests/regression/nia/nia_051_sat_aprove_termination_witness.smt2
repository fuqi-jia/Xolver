; AProVE-style termination: x ≥ 0 ∧ y ≥ 0 ∧ (x+y) ≥ 1 — sat.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= (+ x y) 1))
(check-sat)
