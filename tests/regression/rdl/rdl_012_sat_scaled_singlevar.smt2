; Scaled single-variable RDL: 2x<=3 (=> x<=3/2) and 2x>=3 (=> x>=3/2). Forces x=3/2.
; Single-var __ZERO__ node path with a non-unit coefficient, no rounding.
(set-logic QF_RDL)
(set-info :status sat)
(declare-const x Real)
(assert (<= (* 2 x) 3))
(assert (>= (* 2 x) 3))
(check-sat)
