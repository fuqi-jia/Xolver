; A real square cannot be negative.
(set-logic QF_UFNRA)
(set-info :status unsat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (* (f x) (f x)) (- 1.0)))
(check-sat)
