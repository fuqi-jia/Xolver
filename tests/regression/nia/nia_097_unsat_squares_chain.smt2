; Chain: a² < b² < c² < d² with a≥0 forces strict monotone, then assert d=a+2 with c=a+1 etc — too tight.
; a=0, b=1, c=2, d=3 satisfies. Now add a*d > b*c ⇒ 0 > 2 ⇒ unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const a Int) (declare-const b Int)
(declare-const c Int) (declare-const d Int)
(assert (>= a 0))
(assert (= b (+ a 1)))
(assert (= c (+ a 2)))
(assert (= d (+ a 3)))
(assert (> (* a d) (* b c)))
(check-sat)
