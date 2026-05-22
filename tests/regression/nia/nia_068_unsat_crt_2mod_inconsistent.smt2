; 2-mod inconsistent: x ≡ 0 (mod 4) ∧ x ≡ 1 (mod 2). Inconsistent (4 ⇒ 0, but 0 mod 2 = 0 ≠ 1).
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (mod x 4) 0))
(assert (= (mod x 2) 1))
(check-sat)
