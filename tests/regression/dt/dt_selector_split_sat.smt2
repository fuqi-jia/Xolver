; Selector-driven exhaustiveness split: head(x) is read but x's constructor is
; unknown. The split x = cons(head x, tail x) ∨ x = nil determines x; either
; branch satisfies head(x)=red -> sat. Recovered (was unknown before tier-3).
(set-info :status sat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))
(declare-const x Lst)
(assert (= (head x) red))
(check-sat)
