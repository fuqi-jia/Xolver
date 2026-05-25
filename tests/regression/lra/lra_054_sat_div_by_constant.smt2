; Division by a constant is linear: x/2 <= 5 (=> x <= 10) with x >= 8 is sat.
; Regression for the Kind::Div linearization fix (extractLinearExpr only handled
; const/const before, so (/ x 2) was dropped and the solver returned unknown).
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (<= (/ x 2) 5))
(assert (>= x 8))
(check-sat)
