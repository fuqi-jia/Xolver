; A read pinned to x with x*x=2 has no integer solution.
(set-logic QF_ANIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(assert (= (select a 0) x))
(assert (= (* x x) 2))
(check-sat)
