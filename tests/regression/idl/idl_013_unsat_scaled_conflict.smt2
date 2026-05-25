; Scaled IDL: 2x-2y<=3 (=> x-y<=1) and 2x-2y>=4 (=> x-y>=2). Contradiction.
(set-logic QF_IDL)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- (* 2 x) (* 2 y)) 3))
(assert (>= (- (* 2 x) (* 2 y)) 4))
(check-sat)
