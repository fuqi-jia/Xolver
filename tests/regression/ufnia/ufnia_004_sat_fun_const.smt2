; Function applied to constant in NIA
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(assert (= (f 2) 4))
(assert (= (f 2) (* 2 2)))
(check-sat)
