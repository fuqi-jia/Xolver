; Combinatorial: n!=24 for n=4, n!=120 for n=5. Encode via product: x*(x-1)*(x-2)*(x-3) = 24 ⇒ x=4.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 1)) (assert (<= x 10))
(assert (= (* x (* (- x 1) (* (- x 2) (- x 3)))) 24))
(check-sat)
