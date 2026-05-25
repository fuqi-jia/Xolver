; Boolean equality (= b (or p q)) mixed with arithmetic in QF_LIRA.
; p,q false => b must be false, but b is asserted true => unsat.
; Regression for the atomizer routing boolean equalities to the arithmetic
; extractor (then reporting "unsupported theory atom" -> unknown).
(set-logic QF_LIRA)
(set-info :status unsat)
(declare-const b Bool)
(declare-const p Bool)
(declare-const q Bool)
(declare-const x Real)
(declare-const i Int)
(assert (= b (or p q)))
(assert b)
(assert (not p))
(assert (not q))
(assert (>= i x))
(assert (<= i 5))
(check-sat)
