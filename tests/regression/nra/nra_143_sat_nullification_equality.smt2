(set-logic QF_NRA)
(set-info :status sat)
; Nullification soundness (other direction): at x=1, (x-1)*(y-2) is identically 0,
; so the equality is ALWAYS TRUE on the section and y<0 is satisfiable → SAT. A
; recovery that wrongly constrains the residual to y=2 would give a false UNSAT.
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 1))
(assert (= (* (- x 1) (- y 2)) 0))
(assert (< y 0))
(check-sat)
