; Three vars: two int, one real, single nonlinear bridge.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const j Int)
(declare-const r Real)
(assert (= i 2)) (assert (= j 3))
(assert (= r (/ (to_real i) (to_real j))))
(check-sat)
