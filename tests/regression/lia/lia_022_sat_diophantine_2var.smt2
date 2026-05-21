; 3x + 5y = 7 has integer solutions (e.g. x=4, y=-1).
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 3 x) (* 5 y)) 7))
(check-sat)
