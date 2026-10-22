(set-logic LIA)
(set-info :status unsat)
(assert (exists ((p Bool)) (forall ((q Bool)) (distinct true false false false))))
(check-sat)
