; 4-mod CRT: x ≡ 1 (mod 2) ∧ x ≡ 2 (mod 3) ∧ x ≡ 3 (mod 5) ∧ x ≡ 4 (mod 7).
; CRT gives x ≡ 53 (mod 210). Witness x=53. SAT.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 0)) (assert (< x 210))
(assert (= (mod x 2) 1))
(assert (= (mod x 3) 2))
(assert (= (mod x 5) 3))
(assert (= (mod x 7) 4))
(check-sat)
