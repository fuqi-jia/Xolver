; UFNIA: fn evaluated on x^2 = 4 has contradictory bound.
(set-logic QF_UFNIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= (* x x) 4))
(assert (= (f x) (f 2)))
(assert (distinct (f x) (f 2)))
(check-sat)
