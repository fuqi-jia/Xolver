; f(x)^2 = 10 has no integer solution.
(set-logic QF_UFNIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (* (f x) (f x)) 10))
(check-sat)
