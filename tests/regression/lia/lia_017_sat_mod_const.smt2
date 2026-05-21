; x mod 3 = 1 with 0 ≤ x ≤ 10 — sat (x ∈ {1, 4, 7, 10}).
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (= (mod x 3) 1))
(assert (>= x 0))
(assert (<= x 10))
(check-sat)
