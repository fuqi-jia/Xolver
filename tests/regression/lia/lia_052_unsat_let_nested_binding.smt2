; Nested-in-binding let where the inner let MUST be expanded correctly: a
; depends on x through the inner binding b. a = (x+1)+1 = x+2; with x=0, a=2 != 5.
; UNSAT. A wrong/dropped expansion of the nested let would change a's value and
; could yield a spurious SAT, so this guards expansion CORRECTNESS, not just
; non-unknown.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-fun x () Int)
(assert (let ((a (let ((b (+ x 1))) (+ b 1)))) (and (= a 5) (= x 0))))
(check-sat)
