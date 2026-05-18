(set-logic QF_LIRA)
(declare-const x Real)
(assert (= (to_int (* x x)) 3))
(check-sat)
