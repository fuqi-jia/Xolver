(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a (_ BitVec 1))) (exists ((b (_ BitVec 1))) (bvslt (bvadd a b) (_ bv1 1)))))
(check-sat)
