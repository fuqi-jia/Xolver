; Finite-datatype cardinality (pigeonhole): 4 Color values pairwise distinct,
; but Color has only 3 constructors -> unsat. Refuted by the exhaustiveness
; constructor-split: each var is split is_red/green/blue; distinct forces 4
; different constructors among 3 -> clash on every branch -> unsat.
(set-info :status unsat)
(set-logic QF_UFDT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(declare-const d Color)
(assert (distinct a b c d))
(check-sat)
