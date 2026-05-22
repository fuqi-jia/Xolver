; (x²-4)² = 0 has double roots at ±2. Strict x > 0 picks x=2.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* (- (* x x) 4) (- (* x x) 4)) 0))
(assert (> x 0))
(check-sat)
