; (x-1)^2 > 0 AND x = 1 is unsat. Tests CDCAC sample-on-the-boundary detection
; — sample point at the root must be excluded by strict ineq.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (> (* (- x 1) (- x 1)) 0))
(assert (= x 1))
(check-sat)
