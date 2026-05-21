; 0*x*x > 0 has no solution.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (> (* 0 (* x x)) 0))
(check-sat)
