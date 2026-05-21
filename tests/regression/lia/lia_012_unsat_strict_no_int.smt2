; In Z, x>0 and x<1 is empty (no integer in (0,1)).
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (> x 0))
(assert (< x 1))
(check-sat)
