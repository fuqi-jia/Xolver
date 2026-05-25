; x^2 = 2 — sat, witness is the irrational algebraic number sqrt(2).
; Exercises the RealValue model funnel: NRA exports x as an exact algebraic
; RealValue (defining poly x^2-2 + isolation interval) rather than a lossy
; string. (get-value prints a rational approximation until the exact
; root-obj output mode lands.)
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
