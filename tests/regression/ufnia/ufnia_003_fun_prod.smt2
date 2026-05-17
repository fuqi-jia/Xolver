; Function values multiplied
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun x () Int)
(assert (= (* (f x) (g x)) 12))
(assert (> (f x) 0))
(assert (> (g x) 0))
(check-sat)
