; Scaled single-variable IDL: 3x>=6 (=> x>=2) and 3x<=6 (=> x<=2). Forces x=2.
; Exercises the single-var __ZERO__ node path with a non-unit coefficient.
(set-logic QF_IDL)
(set-info :status sat)
(declare-const x Int)
(assert (>= (* 3 x) 6))
(assert (<= (* 3 x) 6))
(check-sat)
