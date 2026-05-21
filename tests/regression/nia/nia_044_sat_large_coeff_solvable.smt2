; 100x + 99y = 1 sat (x=1, y=-1).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 100 x) (* 99 y)) 1))
(check-sat)
