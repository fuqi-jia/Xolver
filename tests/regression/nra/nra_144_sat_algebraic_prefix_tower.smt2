(set-logic QF_NRA)
(set-info :status sat)
; Algebraic-prefix routing: x=±sqrt(2) makes x*y-1 carry an algebraic coefficient,
; so specialization to a rational univariate fails and the cell MUST be built via
; the algebraic-capable tower/Norm path. The misplaced vanishesAtPrefix gate used
; to return Unknown for any algebraic prefix and bail ("vanish-unknown") BEFORE
; that path; this case guards that algebraic prefixes are routed to the tower path
; instead. SAT witness: x=sqrt(2), y=1/sqrt(2)≈0.707 < 1.
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x x) 2))
(assert (= (* x y) 1))
(assert (< y 1))
(check-sat)
