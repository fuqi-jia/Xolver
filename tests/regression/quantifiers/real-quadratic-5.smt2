(set-logic ALL)
(set-info :status unsat)
(assert (forall ((x Real)) (exists ((y Real)) (= (+ (* (- 2) y y) (* (- 2) x y) (- 1)) 0))))
(check-sat)
