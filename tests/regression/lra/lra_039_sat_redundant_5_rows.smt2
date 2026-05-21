; 5 rows, all redundant scalings of one — degenerate basis stress.
(set-logic QF_LRA)

(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (>= (+ x y) 1))
(assert (>= (+ (* 2 x) (* 2 y)) 2))
(assert (>= (+ (* 3 x) (* 3 y)) 3))
(assert (>= (+ (* 4 x) (* 4 y)) 4))
(assert (>= (+ (* 5 x) (* 5 y)) 5))
(assert (<= x 10))
(check-sat)
