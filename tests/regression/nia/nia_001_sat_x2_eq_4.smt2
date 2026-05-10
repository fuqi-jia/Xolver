(set-logic QF_NIA)
(declare-const x Int)
(assert (= (* x x) 4))
(check-sat)
