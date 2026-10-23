(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 2))) (exists ((b (_ BitVec 2))) (= (bvurem a b) (_ bv0 2)))))
(check-sat)
