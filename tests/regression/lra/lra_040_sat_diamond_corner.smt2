; Forces basis through a degenerate corner where 3 constraints meet.
(set-logic QF_LRA)

(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ x y) 2))
(assert (<= (+ x (- y)) 2))
(assert (<= (+ (- x) y) 2))
(assert (>= (+ (- x) (- y)) 5))  ; violates the diamond at the origin
(check-sat)
