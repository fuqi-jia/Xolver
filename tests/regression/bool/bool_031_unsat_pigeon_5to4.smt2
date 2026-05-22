; Larger pigeonhole 5→4 — exercises CDCL clause learning + restart.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p11 Bool)(declare-const p12 Bool)(declare-const p13 Bool)(declare-const p14 Bool)
(declare-const p21 Bool)(declare-const p22 Bool)(declare-const p23 Bool)(declare-const p24 Bool)
(declare-const p31 Bool)(declare-const p32 Bool)(declare-const p33 Bool)(declare-const p34 Bool)
(declare-const p41 Bool)(declare-const p42 Bool)(declare-const p43 Bool)(declare-const p44 Bool)
(declare-const p51 Bool)(declare-const p52 Bool)(declare-const p53 Bool)(declare-const p54 Bool)
(assert (or p11 p12 p13 p14)) (assert (or p21 p22 p23 p24))
(assert (or p31 p32 p33 p34)) (assert (or p41 p42 p43 p44))
(assert (or p51 p52 p53 p54))
; hole 1: at most one of p11..p51
(assert (not (and p11 p21))) (assert (not (and p11 p31))) (assert (not (and p11 p41))) (assert (not (and p11 p51)))
(assert (not (and p21 p31))) (assert (not (and p21 p41))) (assert (not (and p21 p51)))
(assert (not (and p31 p41))) (assert (not (and p31 p51))) (assert (not (and p41 p51)))
; hole 2
(assert (not (and p12 p22))) (assert (not (and p12 p32))) (assert (not (and p12 p42))) (assert (not (and p12 p52)))
(assert (not (and p22 p32))) (assert (not (and p22 p42))) (assert (not (and p22 p52)))
(assert (not (and p32 p42))) (assert (not (and p32 p52))) (assert (not (and p42 p52)))
; hole 3
(assert (not (and p13 p23))) (assert (not (and p13 p33))) (assert (not (and p13 p43))) (assert (not (and p13 p53)))
(assert (not (and p23 p33))) (assert (not (and p23 p43))) (assert (not (and p23 p53)))
(assert (not (and p33 p43))) (assert (not (and p33 p53))) (assert (not (and p43 p53)))
; hole 4
(assert (not (and p14 p24))) (assert (not (and p14 p34))) (assert (not (and p14 p44))) (assert (not (and p14 p54)))
(assert (not (and p24 p34))) (assert (not (and p24 p44))) (assert (not (and p24 p54)))
(assert (not (and p34 p44))) (assert (not (and p34 p54))) (assert (not (and p44 p54)))
(check-sat)
