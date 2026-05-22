; Two vars with mod constraints: x mod 3 = y mod 3 ∧ x = 7 ∧ y ≥ 0.
; 7 mod 3 = 1, so y mod 3 = 1. Witness y = 1.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= x 7))
(assert (>= y 0))
(assert (= (mod x 3) (mod y 3)))
(check-sat)
