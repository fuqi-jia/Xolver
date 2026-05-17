(set-logic QF_NIA)
(declare-const x Int)
(assert (= (* x x x) 8))
(check-sat)
