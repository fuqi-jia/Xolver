; Multiple functions with shared args
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun x () Int)
(assert (= (+ (f x) (g x)) 10))
(assert (>= (f x) 0))
(assert (>= (g x) 0))
(check-sat)
