(set-logic ALL)
(set-info :status unsat)
(assert (forall ((x Real)) (exists ((y Real)) (= (+ (* (- 1) y y) (* 3 x y) (- 3)) 0))))
(check-sat)
