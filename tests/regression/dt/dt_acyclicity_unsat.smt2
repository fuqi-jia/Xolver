; Acyclicity (recursive datatype): x = cons(h, x) makes x a proper subterm of
; itself, which the free-algebra acyclicity axiom forbids -> unsat.
(set-info :status unsat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))
(declare-const x Lst)
(declare-const h Color)
(assert (= x (cons h x)))
(check-sat)
