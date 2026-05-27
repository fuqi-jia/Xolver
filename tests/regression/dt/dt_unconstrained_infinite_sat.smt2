; Unconstrained INFINITE datatype vars: x != y over an (infinite, recursive)
; list type. No selector reads them and the sort is infinite, so the classes
; are FREE — any distinct values satisfy. sat without splitting (the determinacy
; gate exempts free infinite classes).
(set-info :status sat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))
(declare-const x Lst)
(declare-const y Lst)
(assert (distinct x y))
(check-sat)
