; Atomizer routing: pure-linear constraint under NIRA logic should still solve.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const i Int)
(declare-const r Real)
(assert (<= i 10))
(assert (>= r 0))
(assert (<= (+ (to_real i) r) 100))
(check-sat)
