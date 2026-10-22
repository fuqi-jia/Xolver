(set-logic QF_NIA)
(set-info :status sat)
; Satisfying assignment: b=1, x=1, y=2, q=2, r=0.
; A polynomial remainder of 1 modulo b does not force the integer r to be 1.
(declare-const b Int)
(declare-const x Int)
(declare-const y Int)
(declare-const q Int)
(declare-const r Int)
(assert (= (* x y) (+ (* b q) r)))
(assert (= (* x y) (+ (* b b) 1)))
(assert (distinct r 1))
(check-sat)
