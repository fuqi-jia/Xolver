(set-logic QF_NIA)
(set-info :status unsat)
; product-positivity: a*b >= 1 with a,b >= 0 forces a>=1 and b>=1;
; but b is pinned to 0, so the system is UNSAT (a*b would be 0, not >= 1).
; Refuted soundly by the bound-free product-positivity rule (ZOLVER_NIA_REFUTE).
(declare-const a Int)
(declare-const b Int)
(assert (>= a 0))
(assert (>= b 0))
(assert (= b 0))
(assert (>= (* a b) 1))
(check-sat)
(exit)
