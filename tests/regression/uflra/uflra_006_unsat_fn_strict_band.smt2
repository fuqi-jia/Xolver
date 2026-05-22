; Real-valued fn squeezed empty.
(set-logic QF_UFLRA)
(set-info :status unsat)
(set-info :status unsat)
(declare-fun g (Real) Real)
(assert (> (g 0.0) 5))
(assert (< (g 0.0) 5))
(check-sat)
