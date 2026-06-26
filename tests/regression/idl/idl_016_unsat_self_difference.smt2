; #81 — integer analog of the self-difference fix. (> (- x x) 14) is 0 > 14 =
; false, so the conjunction is unsat. Before the fix the IDL normalizer floored
; the whole check to unknown on the zero-term LHS; now it evaluates the constant
; directly -> a one-literal ImmediateConflict.
(set-logic QF_IDL)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= (- x y) 3))
(assert (> (- x x) 14))
(check-sat)
