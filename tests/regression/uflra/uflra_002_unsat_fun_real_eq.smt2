; Function congruence in reals: f(x) > f(y) but x = y
(set-logic QF_UFLRA)
(set-info :status unsat)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (> (f x) (f y)))
(check-sat)
