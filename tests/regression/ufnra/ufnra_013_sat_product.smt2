; Product of two UF images equals a positive real.
(set-logic QF_UFNRA)
(set-info :status sat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (* (f x) x) 6.0))
(assert (= x 2.0))
(check-sat)
