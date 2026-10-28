; x=10, y=1 refutes a product-conflict explanation that omits y>=2.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 10))
(assert (>= x 6))
(check-sat)
