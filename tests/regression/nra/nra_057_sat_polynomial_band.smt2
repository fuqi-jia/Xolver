; Polynomial constrained to thin band [a, a+eps] — precision sensitive.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= y (* x x)))
(assert (>= y (/ 1 100)))
(assert (<= y (/ 1 99)))
(check-sat)
