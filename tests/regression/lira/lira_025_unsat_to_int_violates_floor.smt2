; Floor property: r - 1 < to_int(r) ≤ r. Violate by asserting to_int r > r.
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const r Real)
(declare-const i Int)
(assert (= i (to_int r)))
(assert (> (to_real i) r))
(check-sat)
