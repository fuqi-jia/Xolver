; (div x 3)=2 and (mod x 3)=1 pin x to 7.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (div x 3) 2))
(assert (= (mod x 3) 1))
(check-sat)
