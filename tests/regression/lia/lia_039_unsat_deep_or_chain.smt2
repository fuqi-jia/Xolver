; Deep or-chain forcing tight value.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (or (= x 1) (= x 2) (= x 3)))
(assert (or (= x 4) (= x 5) (= x 6)))
(check-sat)
