(set-logic ALL)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Real)) (= (+ (* 3 y y) (* (- 3) x y) 0) 0))))
(check-sat)
