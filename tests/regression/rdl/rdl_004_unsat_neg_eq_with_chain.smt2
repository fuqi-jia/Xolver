; Chain forces x = y but ¬(x-y = 0).
(set-logic QF_RDL)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (- x y) 0))
(assert (<= (- y x) 0))
(assert (not (= (- x y) 0)))
(check-sat)
