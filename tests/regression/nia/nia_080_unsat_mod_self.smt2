; (x mod 5) = (x mod 7) ∧ x ≥ 0 ∧ x < 35. Witness x=0 (both = 0). SAT actually.
; Make it UNSAT: add x mod 5 = 3, x mod 7 = 4.
; 3 ≠ 4, so unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (>= x 0)) (assert (< x 35))
(assert (= (mod x 5) 3))
(assert (= (mod x 7) 4))
(assert (= (mod x 5) (mod x 7)))
(check-sat)
