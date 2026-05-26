(set-logic QF_UF)
(set-info :status unsat)
; a=b=c forces f(a)=f(c) by congruence, contradicting distinct(f(a),f(c)).
; Exercises eager disequality-conflict detection (ZOLVER_UF_DISEQ_WATCH): the
; conflict must form the moment the congruence merge unites f(a) and f(c).
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-fun f (U) U)
(assert (= a b))
(assert (= b c))
(assert (distinct (f a) (f c)))
(check-sat)
