(set-logic QF_UFLIA)
(declare-fun x () Int)
(assert (or (= x 0) (= x 1)))
(check-sat)
