; Deep ITE chain: 5 levels — Rewriter / lowering should not blow up.
(set-logic QF_UF)
(set-info :status sat)
(declare-const c1 Bool) (declare-const c2 Bool) (declare-const c3 Bool)
(declare-const c4 Bool) (declare-const c5 Bool)
(declare-const r Bool)
(assert (= r (ite c1 (ite c2 (ite c3 (ite c4 (ite c5 true false) false) false) false) false)))
(assert r)
(check-sat)
