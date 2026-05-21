; 3D contradictory: sum forced both >= 5 and <= 0.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (>= (+ x y z) 5))
(assert (<= (+ x y z) 0))
(check-sat)
