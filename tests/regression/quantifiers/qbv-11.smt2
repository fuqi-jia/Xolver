(set-logic ALL)
(set-info :status sat)
(assert (forall ((a (_ BitVec 2))) (exists ((b (_ BitVec 2))) (bvult (bvand a b) (_ bv2 2)))))
(check-sat)
