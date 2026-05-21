; r*r = 4 ∧ to_int(r) = 2 forces r = 2 exactly.
(set-logic QF_NIRA)
(set-info :status sat)
(declare-const r Real)
(assert (= (* r r) 4))
(assert (= (to_int r) 2))
(check-sat)
