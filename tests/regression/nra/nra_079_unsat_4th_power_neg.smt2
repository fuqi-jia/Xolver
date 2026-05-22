; (x-1)^4 < 0 — always false. UNSAT. Tests sum-of-squares positivity for high power.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< (* (* (- x 1) (- x 1)) (* (- x 1) (- x 1))) 0))
(check-sat)
