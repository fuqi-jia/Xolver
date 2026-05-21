; Real difference logic: chain inequalities.
(set-logic QF_RDL)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (<= (- x y) (/ 1 2)))
(assert (<= (- y z) (/ 1 2)))
(check-sat)
