; #81 — the Tautology side of the self-difference fix. (>= (- x x) 0) is
; 0 >= 0 = true and must be silently absorbed (NOT a spurious conflict), leaving
; the genuine difference constraint (>= (- x y) 3) satisfiable -> sat.
(set-logic QF_RDL)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= (- x y) 3))
(assert (>= (- x x) 0))
(check-sat)
