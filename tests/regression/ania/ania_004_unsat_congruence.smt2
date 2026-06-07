; Equal indices must give equal reads (array congruence).
(set-logic QF_ANIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= i j))
(assert (not (= (select a i) (select a j))))
(check-sat)
