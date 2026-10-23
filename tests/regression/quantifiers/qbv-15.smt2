(set-logic ALL)
(set-info :status unsat)
(assert (exists ((a (_ BitVec 4))) (forall ((b (_ BitVec 4))) (bvslt (bvsub a b) (_ bv10 4)))))
(check-sat)
