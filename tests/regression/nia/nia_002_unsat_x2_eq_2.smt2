(set-logic QF_NIA)
(declare-const x Int)
(assert (= (* x x) 2))
(check-sat)
