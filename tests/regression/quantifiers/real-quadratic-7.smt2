(set-logic ALL)
(set-info :status unsat)
(assert (forall ((x Real)) (exists ((y Real)) (= (+ (* 3 y y) (* 2 x y) 3) 0))))
(check-sat)
