; Pigeonhole: 3 pigeons, 2 holes -> unsat

(declare-const p1h1 Bool)
(declare-const p1h2 Bool)
(declare-const p2h1 Bool)
(declare-const p2h2 Bool)
(declare-const p3h1 Bool)
(declare-const p3h2 Bool)
; Each pigeon in at least one hole
(assert (or p1h1 p1h2))
(assert (or p2h1 p2h2))
(assert (or p3h1 p3h2))
; Each hole has at most one pigeon
(assert (or (not p1h1) (not p2h1)))
(assert (or (not p1h1) (not p3h1)))
(assert (or (not p2h1) (not p3h1)))
(assert (or (not p1h2) (not p2h2)))
(assert (or (not p1h2) (not p3h2)))
(assert (or (not p2h2) (not p3h2)))
(check-sat)
