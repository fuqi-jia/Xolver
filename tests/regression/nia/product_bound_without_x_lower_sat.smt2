; x=1, y=10 refutes the symmetric explanation that omits x>=6.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 10))
(assert (>= y 2))
(check-sat)
