; Huge modulus: x mod 10^15 = 5 ∧ 0 ≤ x ≤ 10^15.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 0)) (assert (<= x 1000000000000000))
(assert (= (mod x 1000000000000000) 5))
(check-sat)
