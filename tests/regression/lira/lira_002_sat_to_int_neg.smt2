(set-logic QF_LIRA)
(assert (= (to_int (- 1.2)) (- 2)))
(check-sat)
