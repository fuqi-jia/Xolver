(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 3))) (exists ((b (_ BitVec 3))) (bvult (bvxor a b) (_ bv7 3)))))
(check-sat)
