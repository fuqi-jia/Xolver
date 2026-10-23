(set-logic ALL)
(set-info :status sat)
(assert (exists ((x Real)) (exists ((y Real)) (and (= (* x x) 2) (> x 0) (= (* y y) (+ x 1))))))
(check-sat)
