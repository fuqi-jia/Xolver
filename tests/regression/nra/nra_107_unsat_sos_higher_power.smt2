; x⁴ < 0 — higher-power positivity gap.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< (* (* x x) (* x x)) 0))
(check-sat)
