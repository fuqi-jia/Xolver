; Two-step acyclicity cycle: x = cons(h, y) and y = cons(h, x) makes x a
; proper subterm of itself through y -> unsat.
(set-info :status unsat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))
(declare-const x Lst)
(declare-const y Lst)
(declare-const h Color)
(assert (= x (cons h y)))
(assert (= y (cons h x)))
(check-sat)
