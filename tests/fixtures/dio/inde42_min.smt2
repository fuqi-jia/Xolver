; Minimal distillation of in-de42 (QF_ANIA AutomizerLoopAcceleration, unsat).
; z3 4.15.4: unsat in 0.00s via arith-dio-tighten (decisions=1).
; xolver: TO (hangs in nia.bit-blast). RED test for the integer Diophantine
; refutation reasoner (see docs/dio-refutation-spec.md).
; Contradiction: linear-equality chain ⟹ z9 = x2 + 2*y2 - y7 - x9; with the
; pow2-mods x2≡y7≡x9≡0 (mod 2^32) ⟹ mod(z9,2^32) = 2*mod(n1,2^31), which forces
; the ite to 1 ⟹ cnd ≥ 1, contradicting cnd ≤ 0.
(set-logic QF_NIA)
(declare-fun y1 () Int)(declare-fun n1 () Int)(declare-fun x1 () Int)
(declare-fun x2 () Int)(declare-fun y2 () Int)(declare-fun z4 () Int)
(declare-fun x5 () Int)(declare-fun z5 () Int)(declare-fun y7 () Int)
(declare-fun z7 () Int)(declare-fun x9 () Int)(declare-fun z9 () Int)
(declare-fun cnd () Int)(declare-fun f () Int)
(assert (= y1 0))
(assert (= n1 x1))
(assert (= (+ x2 y2) (+ x1 y1)))
(assert (= (mod x2 4294967296) 0))
(assert (= y2 z4))
(assert (= (+ x5 z5) (+ x2 z4)))
(assert (= (+ y7 z7) (+ y2 z5)))
(assert (= (mod y7 4294967296) 0))
(assert (= (+ x5 z7) (+ x9 z9)))
(assert (= (mod x9 4294967296) 0))
(assert (>= cnd f))
(assert (<= (ite (= (mod z9 4294967296) (* (mod n1 2147483648) 2)) 1 0) f))
(assert (<= cnd 0))
(check-sat)
