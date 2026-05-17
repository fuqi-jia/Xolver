(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* (/ 1 2) x) 1))
(check-sat)
