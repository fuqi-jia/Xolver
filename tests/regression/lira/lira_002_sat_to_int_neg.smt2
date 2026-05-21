(set-logic QF_LIRA)
(set-info :status sat)
(assert (= (to_int (- 1.2)) (- 2)))
(check-sat)
