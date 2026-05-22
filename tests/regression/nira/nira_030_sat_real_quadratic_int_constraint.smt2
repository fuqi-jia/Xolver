; r² ≤ 4 with i = to_int r, i = 1 ⇒ r ∈ [1, 2). Combined with r² ≤ 4 ⇒ r ∈ [1, 2).
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const r Real)
(declare-const i Int)
(assert (= i (to_int r)))
(assert (= i 1))
(assert (<= (* r r) 4))
(check-sat)
