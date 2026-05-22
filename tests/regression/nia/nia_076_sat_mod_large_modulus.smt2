; Large modulus: x mod 1000 = 500 ∧ 0 ≤ x ≤ 1000.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 0)) (assert (<= x 1000))
(assert (= (mod x 1000) 500))
(check-sat)
