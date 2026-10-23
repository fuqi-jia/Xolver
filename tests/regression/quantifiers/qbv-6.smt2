(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a (_ BitVec 3))) (forall ((b (_ BitVec 3))) (bvult (bvsrem a b) (_ bv0 3)))))
(check-sat)
