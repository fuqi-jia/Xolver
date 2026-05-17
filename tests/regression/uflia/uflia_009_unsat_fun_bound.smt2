; Function value bounded contradiction
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (>= (f x) 5))
(assert (<= (f x) 3))
(check-sat)
