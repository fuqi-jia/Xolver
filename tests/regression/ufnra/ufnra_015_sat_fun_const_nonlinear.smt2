; UF image with a concrete nonlinear identity.
(set-logic QF_UFNRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (f x) 3.0))
(assert (= (* (f x) (f x)) 9.0))
(check-sat)
