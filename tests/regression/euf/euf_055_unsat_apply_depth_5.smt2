; Deep f-apply chain: distinct(f^5(x), f^5(y)) under x=y.
(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const x U) (declare-const y U)
(assert (= x y))
(assert (distinct (f (f (f (f (f x))))) (f (f (f (f (f y)))))))
(check-sat)
