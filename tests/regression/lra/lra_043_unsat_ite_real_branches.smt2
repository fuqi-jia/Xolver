; ITE with two real constants both clashing with outer eq.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const c Bool)
(declare-const x Real)
(assert (= x (ite c (/ 1 2) (/ 1 3))))
(assert (= x 1))
(check-sat)
