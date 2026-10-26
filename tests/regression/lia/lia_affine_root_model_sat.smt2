; One exact integer witness is x=176344, y=-58704.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ (* 65536 x) (* 196867 y)) 16))
(assert (>= (+ (* 65536 x) (* 196867 y)) 16))
(assert (<= y 7))
(check-sat)
