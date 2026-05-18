(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* (- x 1.0) (- x 1.0)) 0.0))
(check-sat)
