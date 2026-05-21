; to_int rounds toward -∞: to_int(-0.5) = -1.
(set-logic QF_LIRA)
(set-info :status sat)
(declare-const r Real)
(declare-const i Int)
(assert (= r (/ (- 1) 2)))
(assert (= i (to_int r)))
(assert (= i (- 1)))
(check-sat)
