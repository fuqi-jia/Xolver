; x^2 >= 0 always, so x^2 < 0 is unsat even through a UF.
(set-logic QF_UFNRA)
(set-info :status unsat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (f x) (* x x)))
(assert (< (f x) 0.0))
(check-sat)
