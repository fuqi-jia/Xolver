; Boolean equality whose RHS contains an arithmetic predicate, coupling the
; propositional and theory layers: b <=> (p or x<0); b true, p false forces
; x<0; an integer i is squeezed in [x, 0]. Satisfiable (e.g. x=-1, i=-1).
(set-logic QF_LIRA)
(set-info :status sat)
(declare-const b Bool)
(declare-const p Bool)
(declare-const x Real)
(declare-const i Int)
(assert (= b (or p (< x 0))))
(assert b)
(assert (not p))
(assert (>= i x))
(assert (<= i 0))
(check-sat)
