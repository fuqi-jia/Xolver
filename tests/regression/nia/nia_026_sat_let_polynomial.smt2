; let binding for polynomial subexpression.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (let ((sq (* x x))) (= sq 9)))
(check-sat)
