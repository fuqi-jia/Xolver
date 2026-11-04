; Preserve a rational binding below a negated disjunction.
(set-option :produce-models true)
(set-logic QF_UFLRA)
(set-info :status sat)
(declare-const x Real)
(declare-fun f (Real) Real)
(assert (not (or (not (and (= x (/ 3 2)) (= (f x) 7))) false)))
(check-sat)
(get-model)
