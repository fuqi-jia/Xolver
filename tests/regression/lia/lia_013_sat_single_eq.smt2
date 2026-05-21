; Equality pins x.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (= x 7))
(check-sat)
