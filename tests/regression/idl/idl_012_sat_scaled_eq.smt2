; Scaled IDL: 2x-2y<=3 (=> x-y<=floor(3/2)=1) and 2y-2x<=-2 (=> x-y>=ceil(2/2)=1).
; Forces x-y=1. Exercises coefficient scaling (coeffs not +/-1).
(set-logic QF_IDL)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- (* 2 x) (* 2 y)) 3))
(assert (<= (- (* 2 y) (* 2 x)) (- 2)))
(check-sat)
