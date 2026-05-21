; i + r > 10 with i ≤ 1 and r ≤ 1 is unsat.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const i Int)
(declare-const r Real)
(assert (<= i 1))
(assert (<= r 1))
(assert (> (+ (to_real i) r) 10))
(check-sat)
