(set-logic QF_ALIA)
(set-info :status unsat)
; Row2 over DISTINCT CONSTANT indices (1 != 2 unconditionally):
;   select(store(a,1,v),2) = select(a,2)
; Asserting its negation is unsatisfiable. Exercises ZOLVER_AX_ROW2_CONST,
; which derives the read equality eagerly (no SAT split) when ON, and the
; standard Row2 lemma when OFF.
(declare-const a (Array Int Int))
(declare-const v Int)
(assert (not (= (select (store a 1 v) 2) (select a 2))))
(check-sat)
