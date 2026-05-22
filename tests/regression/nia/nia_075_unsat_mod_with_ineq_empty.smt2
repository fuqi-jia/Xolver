; x mod 10 = 7 ∧ 0 ≤ x ≤ 6 — empty (smallest residue 7 > 6).
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (>= x 0)) (assert (<= x 6))
(assert (= (mod x 10) 7))
(check-sat)
