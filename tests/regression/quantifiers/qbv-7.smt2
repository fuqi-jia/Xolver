(set-logic ALL)
(set-info :status sat)
(assert (exists ((a (_ BitVec 4))) (exists ((b (_ BitVec 4))) (bvslt (bvsmod a b) (_ bv12 4)))))
(check-sat)
