; Mixed DT + nonlinear-int (the plan's worked example A, made unsat):
;   x = cons(a, nil)  =>  head(x) = a   (DT selector projection)
; then  a > 0  and  head(x) < 0  contradict via the shared Int equality.
; Exercises DT structure owner -> NIA field-value owner sharing through the
; e-graph. If combination is incomplete this floors to unknown (sound); the
; target verdict is unsat.
(set-info :status unsat)
(set-logic QF_UFDTNIA)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(declare-const x Lst)
(declare-const a Int)
(assert (= x (cons a nil)))
(assert (> a 0))
(assert (< (head x) 0))
(check-sat)
