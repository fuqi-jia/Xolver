(set-logic ALL)
(set-info :status sat)
(assert (forall ((x Real)) (exists ((y Real)) (= (+ (* (- 2) y y) (* 3 x y) 1) 0))))
(check-sat)
