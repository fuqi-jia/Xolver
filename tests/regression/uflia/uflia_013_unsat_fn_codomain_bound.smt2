; f(0) constrained by both bounds — unsat.
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(assert (>= (f 0) 10))
(assert (<= (f 0) 5))
(check-sat)
