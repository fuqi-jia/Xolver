; Two equalities with different constants.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= x 5))
(assert (= x 6))
(check-sat)
