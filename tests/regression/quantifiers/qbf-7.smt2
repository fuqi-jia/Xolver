(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Bool)) (forall ((b Bool)) (exists ((c Bool)) (or (and (not a) (not b) (not c)) (and (not a) b (not c)) (and a b c))))))
(check-sat)
