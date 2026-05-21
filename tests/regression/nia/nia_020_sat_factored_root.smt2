; (x-2)(x-3) = 0 has integer roots 2 and 3.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (* (- x 2) (- x 3)) 0))
(check-sat)
