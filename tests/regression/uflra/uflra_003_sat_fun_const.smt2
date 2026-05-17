; Function applied to real constant
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(assert (= (f 0.5) 1.0))
(check-sat)
