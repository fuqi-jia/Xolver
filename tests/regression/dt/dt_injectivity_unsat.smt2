; Injectivity: box(p) = box(q) implies p = q, contradicting p != q -> unsat.
; Pure equality reasoning over an enum field (no arithmetic needed).
(set-info :status unsat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Box 0)) (((box (item Color)))))
(declare-const p Color)
(declare-const q Color)
(assert (= (box p) (box q)))
(assert (not (= p q)))
(check-sat)
