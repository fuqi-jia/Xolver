; ITE bridging int / real result types via to_real.
(set-logic QF_LIRA)
(set-info :status sat)
(declare-const c Bool)
(declare-const i Int)
(declare-const r Real)
(assert (= r (ite c (to_real i) (/ 1 2))))
(assert (>= i 0))
(check-sat)
