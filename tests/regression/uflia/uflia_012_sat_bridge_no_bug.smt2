; Control: similar shape but actually sat (no contradiction).
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= x 1))
(assert (= (f x) 5))
(assert (= (f 1) 5))
(check-sat)
