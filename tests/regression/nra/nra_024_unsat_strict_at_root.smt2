; (x-1)^2 < 0 is unsat (squared term is non-negative).
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< (* (- x 1) (- x 1)) 0))
(check-sat)
