; Two ORs with no common satisfier.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (or (< x 0) (> x 10)))
(assert (and (>= x 1) (<= x 9)))
(check-sat)
