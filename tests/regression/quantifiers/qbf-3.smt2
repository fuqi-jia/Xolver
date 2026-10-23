(set-logic ALL)
(set-info :status unsat)
(assert (forall ((a Bool)) (forall ((b Bool)) (forall ((c Bool)) (or (and (not a) (not b) (not c)) (and (not a) (not b) c) (and a (not b) c) (and a b c))))))
(check-sat)
