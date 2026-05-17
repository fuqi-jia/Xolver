(set-logic QF_LRA)
(declare-const x Real)
(assert (= (* 2 x) 1))
(check-sat)
