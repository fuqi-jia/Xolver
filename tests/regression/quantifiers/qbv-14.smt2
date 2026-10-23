(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 4))) (exists ((b (_ BitVec 4))) (bvult (bvadd a b) (_ bv1 4)))))
(check-sat)
