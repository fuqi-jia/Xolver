; Inductive invariant: at any step i, s(i) + r(i) = const.
; Initial s(0)=10, r(0)=0. Transition s' = s-1, r' = r+1. Invariant: s+r=10.
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun s (Int) Int)
(declare-fun r (Int) Int)
(assert (= (s 0) 10)) (assert (= (r 0) 0))
(assert (= (s 1) (- (s 0) 1))) (assert (= (r 1) (+ (r 0) 1)))
(assert (= (s 2) (- (s 1) 1))) (assert (= (r 2) (+ (r 1) 1)))
(assert (= (s 3) (- (s 2) 1))) (assert (= (r 3) (+ (r 2) 1)))
(assert (= (+ (s 3) (r 3)) 10))
(check-sat)
