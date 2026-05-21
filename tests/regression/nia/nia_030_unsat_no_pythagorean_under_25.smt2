; x^2 + y^2 = 11 has no non-negative integer solutions (11 ∉ sum-of-two-squares set).
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x 0)) (assert (<= x 5))
(assert (>= y 0)) (assert (<= y 5))
(assert (= (+ (* x x) (* y y)) 11))
(check-sat)
