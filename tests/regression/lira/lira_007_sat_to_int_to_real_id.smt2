(set-logic QF_LIRA)
(declare-const x Int)
(assert (= (to_int (to_real x)) x))
(check-sat)
