; Scaled RDL: 2x-2y<=3 (=> x-y<=3/2) and 2y-2x<=-2 (=> x-y>=1). Sat: x-y in [1, 3/2].
; Exact rational division, no integer rounding.
(set-logic QF_RDL)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (- (* 2 x) (* 2 y)) 3))
(assert (<= (- (* 2 y) (* 2 x)) (- 2)))
(check-sat)
