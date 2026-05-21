; Conflicting bounds via huge constant — must not overflow.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (>= x (- 9999999999)))
(assert (<= x 9999999999))
(assert (= x 0))
(check-sat)
