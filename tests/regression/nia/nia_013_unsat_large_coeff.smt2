(set-logic QF_NIA)
(declare-const x Int)
(assert (= (* 1000 (* x x)) 1000000))
(check-sat)
