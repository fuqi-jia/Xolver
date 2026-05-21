; Function congruence with arithmetic: f(x) > f(y) but x = y
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (> (f x) (f y)))
(check-sat)
