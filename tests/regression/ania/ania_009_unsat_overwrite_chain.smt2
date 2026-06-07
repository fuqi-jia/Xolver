; Overwrite the same index twice; last write wins.
(set-logic QF_ANIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (not (= (select (store (store a i 1) i 2) i) 2)))
(check-sat)
