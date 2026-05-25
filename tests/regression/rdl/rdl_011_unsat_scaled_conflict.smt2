; Scaled RDL: 2x-2y<=3 (=> x-y<=3/2) and 2x-2y>=4 (=> x-y>=2). Contradiction (3/2 < 2).
(set-logic QF_RDL)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (- (* 2 x) (* 2 y)) 3))
(assert (>= (- (* 2 x) (* 2 y)) 4))
(check-sat)
