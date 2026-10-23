(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a (_ BitVec 3))) (exists ((b (_ BitVec 3))) (bvult (bvmul a b) (_ bv0 3)))))
(check-sat)
