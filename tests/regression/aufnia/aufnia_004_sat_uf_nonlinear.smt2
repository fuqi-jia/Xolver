; UF result squared, stored back into the array.
(set-logic QF_AUFNIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (select (store a 0 (* (f x) (f x))) 0) 25))
(assert (>= (f x) 0))
(check-sat)
