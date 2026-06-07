; Equal reads -> equal f-images (UF congruence); negation is unsat.
(set-logic QF_AUFNIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun f (Int) Int)
(assert (= (select a 0) (select a 1)))
(assert (not (= (f (select a 0)) (f (select a 1)))))
(check-sat)
