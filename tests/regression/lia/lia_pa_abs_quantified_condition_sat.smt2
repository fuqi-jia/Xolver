(set-logic LIA)
(set-info :status sat)
; A quantified condition within a term must not capture its surrounding witness.
(assert (forall ((x Int))
  (= (ite (forall ((y Int)) (>= (+ y x) y)) x (- x)) (abs x))))
(check-sat)
