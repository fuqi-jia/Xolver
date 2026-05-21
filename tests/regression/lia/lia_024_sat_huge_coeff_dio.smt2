; Large coefficients but solvable: 1000x + 999y = 1, (x=1, y=-1).
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 1000 x) (* 999 y)) 1))
(check-sat)
