; UF applied to an array read, with a nonlinear constraint.
(set-logic QF_AUFNIA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun f (Int) Int)
(assert (= (f (select a 0)) 4))
(assert (= (* (select a 0) (select a 0)) 9))
(assert (> (select a 0) 0))
(check-sat)
