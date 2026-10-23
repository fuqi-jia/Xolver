(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Bool)) (exists ((b Bool)) (forall ((c Bool)) (or (and (not a) (not b) (not c)) (and a (not b) (not c)) (and (not a) b (not c)) (and a (not b) c))))))
(check-sat)
