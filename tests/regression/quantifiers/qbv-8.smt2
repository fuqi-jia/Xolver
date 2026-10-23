(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 3))) (forall ((b (_ BitVec 3))) (bvult (bvshl a b) (_ bv2 3)))))
(check-sat)
