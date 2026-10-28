; Both positive lower bounds are necessary for this product contradiction.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 10))
(assert (>= x 6))
(assert (>= y 2))
(check-sat)
