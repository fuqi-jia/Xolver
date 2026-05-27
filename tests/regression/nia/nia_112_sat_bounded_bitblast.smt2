(set-logic QF_NIA)
(set-info :status sat)
; A bounded nonlinear integer system the bit-blast stage decides: x,y in [0,15]
; with x*y = 143 (= 11*13) and x < y. Finite box -> bit-blast finds the model.
; Exercises the bounded-box bit-blast path (incl. the x4 width growth, aaa304a):
; the unique solution x=11,y=13 needs widths past the narrowest iteration.
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0)) (assert (<= x 15))
(assert (>= y 0)) (assert (<= y 15))
(assert (< x y))
(assert (= (* x y) 143))
(check-sat)
(exit)
