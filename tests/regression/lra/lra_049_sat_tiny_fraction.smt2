; Rational underflow: x = 1/10^18 — must be exact.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (= x (/ 1 1000000000000000000)))
(assert (> x 0))
(check-sat)
