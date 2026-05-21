; x^3 = 27 has integer root x = 3.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (* x (* x x)) 27))
(check-sat)
