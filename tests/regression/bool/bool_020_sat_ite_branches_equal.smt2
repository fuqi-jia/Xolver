; ite(c, p, p) simplifies to p regardless of c.
(set-logic QF_UF)
(set-info :status sat)
(declare-const c Bool)
(declare-const p Bool)
(assert (= (ite c p p) p))
(check-sat)
