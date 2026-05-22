; Ellipse x²/4 + y² = 1 ∩ Hyperbola x² - y² = 1. Solve: from H, x²=1+y².
; Plug in: (1+y²)/4 + y² = 1 ⇒ 5y²/4 = 3/4 ⇒ y² = 3/5; x² = 8/5. SAT.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ (/ (* x x) 4) (* y y)) 1))
(assert (= (- (* x x) (* y y)) 1))
(check-sat)
