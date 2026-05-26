(set-logic QF_ALRA)
(set-info :status unsat)
; 1.0 and 1 denote the SAME real index, so by Row1
;   select(store(a,1.0,v),1) = v
; and Row2 must NOT fire (it requires the indices to be distinct). Guards
; ZOLVER_AX_ROW2_CONST against treating equal-valued reals with different
; textual forms ("1.0" vs "1") as distinct indices. Asserting != v is unsat.
(declare-const a (Array Real Real))
(declare-const v Real)
(assert (not (= (select (store a 1.0 v) 1) v)))
(check-sat)
