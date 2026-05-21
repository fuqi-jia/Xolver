; (=> p (>= x 5)) ∧ p ∧ (< x 5) — must be unsat.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const p Bool)
(declare-const x Int)
(assert (=> p (>= x 5)))
(assert p)
(assert (< x 5))
(check-sat)
