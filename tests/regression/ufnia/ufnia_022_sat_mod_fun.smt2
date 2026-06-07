; mod-by-constant of a function image.
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (mod (f x) 4) 3))
(assert (>= (f x) 0))
(assert (<= (f x) 20))
(check-sat)
