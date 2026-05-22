; CRT: x ≡ 2 (mod 3) ∧ x ≡ 3 (mod 5) ∧ x ≡ 2 (mod 7), 0 ≤ x < 105.
; x = 23 satisfies (23 mod 3 = 2, mod 5 = 3, mod 7 = 2). SAT.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 0))
(assert (< x 105))
(assert (= (mod x 3) 2))
(assert (= (mod x 5) 3))
(assert (= (mod x 7) 2))
(check-sat)
