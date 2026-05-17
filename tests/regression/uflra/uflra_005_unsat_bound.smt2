; Contradictory bounds on function value
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (>= (f x) 5.0))
(assert (<= (f x) 3.0))
(check-sat)
