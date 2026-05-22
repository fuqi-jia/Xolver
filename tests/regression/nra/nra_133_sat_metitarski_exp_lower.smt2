; Meti-tarski exp(x) lower bound: 1 + x ≤ exp(x) — sat means 1+x ≤ exp_approx.
; exp_approx = 1 + x + x²/2 + x³/6 for x ∈ [0,1]. 1+x ≤ 1+x+x²/2+x³/6 ⇒ 0 ≤ x²/2+x³/6, true.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const exp_x Real)
(assert (>= x 0))
(assert (<= x 1))
(assert (= exp_x (+ 1 x (/ (* x x) 2) (/ (* x (* x x)) 6))))
(assert (>= exp_x (+ 1 x)))
(check-sat)
