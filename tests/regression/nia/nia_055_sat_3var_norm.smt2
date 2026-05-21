; 3-var norm with explicit witness (1,0,0).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (>= (+ (* a a) (* b b) (* c c)) 1))
(assert (<= (+ (* a a) (* b b) (* c c)) 10))
(check-sat)
