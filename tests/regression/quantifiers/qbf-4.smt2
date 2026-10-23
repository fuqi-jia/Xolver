(set-logic ALL)
(set-info :status sat)
(assert (forall ((a Bool)) (exists ((b Bool)) (exists ((c Bool)) (or (and a (not b) (not c)) (and (not a) b (not c)) (and (not a) (not b) c))))))
(check-sat)
