; Scaled strict RDL: 2x-2y<3 (=> x-y<3/2) and 2x-2y>3 (=> x-y>3/2). Contradiction.
; Exercises the strict-delta weight RdlWeight(3/2, -1) on a scaled bound.
(set-logic QF_RDL)
(set-info :status unsat)
(declare-const x Real)
(declare-const y Real)
(assert (< (- (* 2 x) (* 2 y)) 3))
(assert (> (- (* 2 x) (* 2 y)) 3))
(check-sat)
