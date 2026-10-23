(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 4))) (exists ((b (_ BitVec 4))) (= (bvlshr a b) (_ bv14 4)))))
(check-sat)
