(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a (_ BitVec 2))) (forall ((b (_ BitVec 2))) (bvslt (bvsub a b) (_ bv2 2)))))
(check-sat)
