; RDL negative cycle.
(set-logic QF_RDL)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (- x y) (/ (- 1) 2)))
(assert (<= (- y x) (/ (- 1) 2)))
(check-sat)
