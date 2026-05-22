; State machine with array-like UF: state s, transition next(s) = s+1 if s<5 else 0.
; 5 unrolling steps from initial state 0. Final state should reach 5 → 0 cycle.
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun s (Int) Int)
(assert (= (s 0) 0))
(assert (= (s 1) (ite (< (s 0) 5) (+ (s 0) 1) 0)))
(assert (= (s 2) (ite (< (s 1) 5) (+ (s 1) 1) 0)))
(assert (= (s 3) (ite (< (s 2) 5) (+ (s 2) 1) 0)))
(assert (= (s 4) (ite (< (s 3) 5) (+ (s 3) 1) 0)))
(assert (= (s 5) (ite (< (s 4) 5) (+ (s 4) 1) 0)))
(assert (= (s 5) 5))
(check-sat)
