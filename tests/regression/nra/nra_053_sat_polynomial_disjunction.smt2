; Disjunction of polynomial constraints — both branches sat.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (or (>= (* x x) 100) (<= (* x x) (/ 1 100))))
(check-sat)
