(set-logic ALL)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Real)) (= (+ (* 1 y y) (* (- 1) x y) (- 2)) 0))))
(check-sat)
