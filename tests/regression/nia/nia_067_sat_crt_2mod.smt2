; 2-mod CRT: x ≡ 1 (mod 2) ∧ x ≡ 2 (mod 3), x ∈ [0, 6). Witness x=5.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 0)) (assert (< x 6))
(assert (= (mod x 2) 1))
(assert (= (mod x 3) 2))
(check-sat)
