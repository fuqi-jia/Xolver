; All bounds and one redundant 0-objective row (introduced by elimination).
(set-logic QF_LRA)

(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (- x y) 0))
(assert (= (- y x) 0))
(assert (>= x 0))
(assert (<= x 10))
(check-sat)
