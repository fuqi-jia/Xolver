(set-logic QF_LIRA)
(declare-fun x () Int)
(assert (= (* 2 x) 1))
(check-sat)
