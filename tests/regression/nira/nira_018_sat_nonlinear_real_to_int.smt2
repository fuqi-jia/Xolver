; (to_int (r*r+1)) ≥ 1 always when r is any real.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const r Real)
(declare-const i Int)
(assert (= i (to_int (+ (* r r) 1))))
(assert (>= i 1))
(check-sat)
