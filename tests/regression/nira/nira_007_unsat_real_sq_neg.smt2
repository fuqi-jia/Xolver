; r*r = -1 has no real solution.
(set-logic QF_NIRA)
(set-info :status unsat)
(declare-const r Real)
(declare-const i Int)
(assert (= (* r r) (to_real (- 1))))
(check-sat)
