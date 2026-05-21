; to_int(to_real(i)) = i for any integer.
(set-logic QF_LIRA)
(set-info :status sat)
(declare-const i Int)
(assert (= (to_int (to_real i)) i))
(check-sat)
