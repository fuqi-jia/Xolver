; (x mod 4) = 1 ∧ (x div 4) = 2 — pins x = 9.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (mod x 4) 1))
(assert (= (div x 4) 2))
(check-sat)
