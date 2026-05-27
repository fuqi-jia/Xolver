; Guarded selector soundness: head(nil) is UNDERSPECIFIED (any value), not a
; conflict. x = nil and head(x) = red is satisfiable. Every datatype class is
; constructor-determined (x=nil, head(x)=red), so Zolver returns a sound sat.
(set-info :status sat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))
(declare-const x Lst)
(assert (= x nil))
(assert (= (head x) red))
(check-sat)
