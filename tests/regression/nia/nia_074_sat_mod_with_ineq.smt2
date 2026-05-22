; x mod 7 = 3 ∧ 20 ≤ x ≤ 30 — witnesses {24}, sat.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x 20)) (assert (<= x 30))
(assert (= (mod x 7) 3))
(check-sat)
