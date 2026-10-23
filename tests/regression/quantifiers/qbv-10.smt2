(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a (_ BitVec 4))) (exists ((b (_ BitVec 4))) (= (bvashr a b) (_ bv7 4)))))
(check-sat)
