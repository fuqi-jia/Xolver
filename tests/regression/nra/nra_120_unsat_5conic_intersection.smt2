; Five conic curves: 2 circles + 2 ellipses + 1 hyperbola sharing common region only outside their pairwise intersection.
; All 5 simultaneously is provably unsat.
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 1))                 ; unit circle
(assert (= (+ (* (- x 1) (- x 1)) (* y y)) 1))     ; circle at (1,0)
(assert (<= (+ (/ (* x x) 4) (* y y)) 1))          ; horizontal ellipse
(assert (<= (+ (* x x) (/ (* y y) 4)) 1))          ; vertical ellipse
(assert (>= x 2))                                  ; outside both circles
(check-sat)
