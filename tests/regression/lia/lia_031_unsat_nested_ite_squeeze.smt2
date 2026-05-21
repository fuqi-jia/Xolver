; Two nested ITE branches both force x to non-overlapping values, parent constraint excludes both.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const c1 Bool) (declare-const c2 Bool)
(declare-const x Int)
(assert (= x (ite c1 (ite c2 1 2) (ite c2 3 4))))
(assert (>= x 5))
(check-sat)
