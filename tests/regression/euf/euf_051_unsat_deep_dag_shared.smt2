; Deep DAG: under x=y, f(f(f(x))) = f(f(f(y))) by repeated congruence.
; Asserting distinct is unsat. Stresses hash-consing and congruence iteration.
(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const x U)
(declare-const y U)
(assert (= x y))
(assert (distinct (f (f (f x))) (f (f (f y)))))
(check-sat)
