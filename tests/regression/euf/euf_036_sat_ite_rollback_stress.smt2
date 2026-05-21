; Rollback stress test: multiple push/pop cycles with ITE
(set-logic QF_UF)
(set-info :status sat)
(declare-fun c () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)

; Cycle 1: c=true -> result=then
(push)
(assert (= c true))
(assert (distinct (ite c a b) a))
(check-sat)  ; unsat
(pop)

; Cycle 2: c=false -> result=else
(push)
(assert (= c false))
(assert (distinct (ite c a b) b))
(check-sat)  ; unsat
(pop)

; Cycle 3: then=else -> result=then (no cond needed)
(push)
(assert (= a b))
(assert (distinct (ite c a b) a))
(check-sat)  ; unsat
(pop)

; Cycle 4: re-enable c=true after all pops
(push)
(assert (= c true))
(assert (distinct (ite c a b) a))
(check-sat)  ; unsat
(pop)

; Final: consistent state
(assert (= (ite c a b) (ite c a b)))
(check-sat)  ; sat
