; p = (x-1)(x-2), q = (x-3)(x-4). Roots disjoint: {1,2} vs {3,4}. UNSAT.
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const x Real)
(assert (= (* (- x 1) (- x 2)) 0))
(assert (= (* (- x 3) (- x 4)) 0))
(check-sat)
