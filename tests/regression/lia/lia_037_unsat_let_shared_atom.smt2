; let-bound shared atom used positively and negatively.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (let ((a (>= x 10))) (and a (not a))))
(check-sat)
