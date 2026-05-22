; Safety property: ∀i, s(i) ≤ 5. With 5-step unrolling starting at 0.
; If we assert (s 5) > 5 ⇒ unsat (because state monotone with cap).
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun s (Int) Int)
(assert (= (s 0) 0))
(assert (= (s 1) (ite (< (s 0) 5) (+ (s 0) 1) (s 0))))
(assert (= (s 2) (ite (< (s 1) 5) (+ (s 1) 1) (s 1))))
(assert (= (s 3) (ite (< (s 2) 5) (+ (s 2) 1) (s 2))))
(assert (= (s 4) (ite (< (s 3) 5) (+ (s 3) 1) (s 3))))
(assert (= (s 5) (ite (< (s 4) 5) (+ (s 4) 1) (s 4))))
(assert (> (s 5) 5))
(check-sat)
