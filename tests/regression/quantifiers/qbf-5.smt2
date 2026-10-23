(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Bool)) (exists ((b Bool)) (forall ((c Bool)) (or (and (not a) (not b) (not c)) (and a b (not c)) (and a (not b) c) (and (not a) b c) (and a b c))))))
(check-sat)
