; (to_real i) = 1.5 — int cast to real can't equal non-integer.
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const i Int)
(assert (= (to_real i) (/ 3 2)))
(check-sat)
