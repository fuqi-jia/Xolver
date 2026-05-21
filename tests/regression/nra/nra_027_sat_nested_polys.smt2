; Nested polynomial: ((x*x)*x) = x^3 with x in [1,2] — sat.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (>= x 1))
(assert (<= x 2))
(assert (>= (* (* x x) x) 1))
(check-sat)
