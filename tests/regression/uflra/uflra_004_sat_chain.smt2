; Chain of real inequalities with function
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (< (f x) 10.0))
(assert (> (f x) 0.0))
(assert (= x 1.0))
(check-sat)
