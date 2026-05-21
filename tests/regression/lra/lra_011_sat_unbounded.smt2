; Unbounded but satisfiable: single strict lower bound.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (> x 0))
(check-sat)
