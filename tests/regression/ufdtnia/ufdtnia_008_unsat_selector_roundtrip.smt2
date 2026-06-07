; snd(mk x y) = y always; nonlinear y with no integer root makes it unsat.
(set-logic QF_UFDTNIA)
(set-info :status unsat)
(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* (snd (mk x y)) (snd (mk x y))) 5))
(check-sat)
