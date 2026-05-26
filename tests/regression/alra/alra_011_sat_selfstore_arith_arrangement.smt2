; N-O arrangement: two self-store equalities + arith on the element force i0!=i1.
; Was Unknown before model-based arrangement splitting (e83c4b3); now sat.
(set-logic QF_ALRA)
(set-info :status sat)
(declare-const a (Array Real Real))
(declare-const i0 Real)(declare-const i1 Real)(declare-const e0 Real)(declare-const e1 Real)
(assert (= a (store a i0 e0)))
(assert (= a (store a i1 e1)))
(assert (= e1 (+ e0 3.0)))
(check-sat)
