; let-binding hiding a contradiction.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert (let ((q (and p (not p)))) q))
(check-sat)
