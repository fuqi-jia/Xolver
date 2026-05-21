; LassoRanker-style: strict decrease of a multivariate rank.
; (x' < x) ∧ (x ≥ 0) ∧ (x' ≥ 0) — sat (e.g. x=2, x'=1).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const xp Int)
(assert (>= x 0))
(assert (>= xp 0))
(assert (< xp x))
(check-sat)
