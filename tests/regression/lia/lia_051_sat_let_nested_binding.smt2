; A let whose BINDING VALUE contains a nested let (SVCOMP CSE shape).
; a = (x+1)+1 = x+2; a=5 => x=3. SAT.
; Regression: SOMTParser expandLet must expand lets nested inside binding
; values, else the inner let survives as an unmapped node -> false unknown.
(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x () Int)
(assert (let ((a (let ((b (+ x 1))) (+ b 1)))) (= a 5)))
(check-sat)
