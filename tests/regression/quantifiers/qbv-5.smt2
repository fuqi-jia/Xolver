(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a (_ BitVec 1))) (forall ((b (_ BitVec 1))) (bvslt (bvsdiv a b) (_ bv0 1)))))
(check-sat)
