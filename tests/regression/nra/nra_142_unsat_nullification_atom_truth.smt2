(set-logic QF_NRA)
(set-info :status unsat)
; Nullification soundness: at x=1, p=(x-1)*y is identically 0 on the section, so
; p>0 is ALWAYS FALSE → UNSAT. A CAC/Lazard impl that treats the valuation-
; recovered residual (y) as the atom's truth-residual would wrongly return sat.
; Atom truth must use p≡0 directly, NOT the lifting-boundary valuation.
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 1))
(assert (> (* (- x 1) y) 0))
(check-sat)
