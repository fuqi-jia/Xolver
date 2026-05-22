; Huge coefficient: must use GMP arbitrary precision, not int64.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (* 1000000000000000000 x) 1000000000000000000))
(check-sat)
