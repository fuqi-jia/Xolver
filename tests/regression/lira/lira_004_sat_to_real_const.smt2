(set-logic QF_LIRA)
(set-info :status sat)
(assert (= (to_real 3) (/ 3 1)))
(check-sat)
