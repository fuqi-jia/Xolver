; x ≡ 1 (mod 6) ∧ x ≡ 0 (mod 3) — inconsistent (6 mod 3 = 0, so x mod 6 = 1 ⇒ x mod 3 = 1, not 0).
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (mod x 6) 1))
(assert (= (mod x 3) 0))
(check-sat)
