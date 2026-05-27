; Tester-driven reconstruction: is_cons(x) is asserted, head(x)=red. The split
; + tester-consistency pick the cons branch, reconstructing x = cons(head x,
; tail x) (a determined ground model) -> sat. Recovered via tier-3.
(set-info :status sat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Lst 0)) (((cons (head Color) (tail Lst)) (nil))))
(declare-const x Lst)
(assert ((_ is cons) x))
(assert (= (head x) red))
(check-sat)
