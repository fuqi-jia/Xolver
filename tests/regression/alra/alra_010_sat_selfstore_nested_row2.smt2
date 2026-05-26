; Regression: false-UNSAT from Row2 over a self-store class + nested store.
; Two self-store array equalities a=store(a,i,e) plus a 2-layer-store read must
; stay sat (z3/cvc5 agree). Guards the Row2 read-equality-term + i=j-degenerate fixes.
(set-logic QF_ALRA)
(set-info :status sat)
(declare-const a (Array Real Real))
(declare-const i0 Real)(declare-const i1 Real)(declare-const e0 Real)(declare-const e1 Real)
(assert (= a (store a i0 e0)))
(assert (= (select (store (store a i0 (+ e0 3.0)) 1.0 (+ e1 3.0)) i0) e1))
(assert (= a (store (store a i1 e1) i1 e1)))
(check-sat)
