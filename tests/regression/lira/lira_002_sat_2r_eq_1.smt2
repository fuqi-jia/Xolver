(set-logic QF_LIRA)
(declare-fun r () Real)
(assert (= (* 2 r) 1))
(check-sat)
