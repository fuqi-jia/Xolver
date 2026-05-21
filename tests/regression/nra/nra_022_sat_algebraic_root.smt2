; x^2 = 2 has irrational solution x = sqrt(2) ≈ 1.414.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* x x) 2))
(assert (> x 0))
(check-sat)
