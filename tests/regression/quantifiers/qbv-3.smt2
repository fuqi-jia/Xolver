(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 2))) (exists ((b (_ BitVec 2))) (bvult (bvudiv a b) (_ bv1 2)))))
(check-sat)
