; NRA with huge rational coefficient.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* x x) (/ 1 1000000000000)))
(assert (> x 0))
(check-sat)
