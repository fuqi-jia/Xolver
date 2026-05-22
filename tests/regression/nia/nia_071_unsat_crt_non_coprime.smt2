; Non-coprime moduli with conflict: x ≡ 1 (mod 6) ∧ x ≡ 2 (mod 4).
; mod 6 = 1 ⇒ x is odd; mod 4 = 2 ⇒ x is even. Conflict.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (mod x 6) 1))
(assert (= (mod x 4) 2))
(check-sat)
