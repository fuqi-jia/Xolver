; r*r ∈ [4, 4] ⇒ r = ±2, to_int(r) ∈ {-2, 2}.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const r Real)
(declare-const i Int)
(assert (= (* r r) 4))
(assert (= i (to_int r)))
(assert (>= i 0))
(check-sat)
