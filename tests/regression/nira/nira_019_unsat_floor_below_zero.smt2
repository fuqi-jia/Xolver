; r > 0 forces (to_int r) ≥ 0; asserting (to_int r) < 0 is unsat.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const r Real)
(declare-const i Int)
(assert (>= r 0))
(assert (= i (to_int r)))
(assert (< i 0))
(check-sat)
