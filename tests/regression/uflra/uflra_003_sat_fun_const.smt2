; Function applied to real constant
(set-logic QF_UFLRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(assert (= (f 0.5) 1.0))
(check-sat)
