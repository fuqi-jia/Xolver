; let-binding: bind q to (and p1 p2), use in implication.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p1 Bool)
(declare-const p2 Bool)
(assert (let ((q (and p1 p2))) (=> q p1)))
(check-sat)
