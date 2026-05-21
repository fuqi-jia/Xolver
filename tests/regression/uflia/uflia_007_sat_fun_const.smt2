; Function applied to constant
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(assert (= (f 3) 6))
(assert (= (f 3) (* 2 3)))
(check-sat)
