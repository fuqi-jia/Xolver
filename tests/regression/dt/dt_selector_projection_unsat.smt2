; Guarded selector projection: p = mk(a,b) gives fst(p) = a, contradicting
; fst(p) != a -> unsat. The selector fires only because p's class holds a
; constructor of the selector's own constructor (mk).
(set-info :status unsat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((Pair 0)) (((mk (fst Color) (snd Color)))))
(declare-const a Color)
(declare-const b Color)
(declare-const p Pair)
(assert (= p (mk a b)))
(assert (not (= (fst p) a)))
(check-sat)
