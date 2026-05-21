; Linear int part + nonlinear real part. Solver should route appropriately.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const r Real)
(assert (= i 3))
(assert (> r 0))
(assert (= (* r r) (to_real i)))
(check-sat)
