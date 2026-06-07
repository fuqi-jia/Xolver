; Real square root of 2 through a UF image: satisfiable over the reals.
(set-logic QF_UFNRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (* (f x) (f x)) 2.0))
(assert (> (f x) 0.0))
(check-sat)
