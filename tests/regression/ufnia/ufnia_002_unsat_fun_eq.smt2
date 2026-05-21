; Function congruence with NIA: f(x) != f(y) but x = y
(set-logic QF_UFNIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
