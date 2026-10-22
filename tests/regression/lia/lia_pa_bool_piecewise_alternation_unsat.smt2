(set-logic LIA)
(set-info :status unsat)
; An integer witness outside the Boolean quantifier must serve both branches.
(assert (exists ((x Int)) (forall ((p Bool)) (= x (ite p 3 (- 2))))))
(check-sat)
