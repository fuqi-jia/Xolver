(set-logic ALL)
(set-info :status unsat)
(assert (exists ((a (_ BitVec 4))) (forall ((b (_ BitVec 4))) (= (bvor a b) (_ bv2 4)))))
(check-sat)
