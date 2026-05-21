(set-logic QF_LIRA)
(set-info :status unsat)
(assert (= (to_int (- 1.2)) (- 1)))
(check-sat)
