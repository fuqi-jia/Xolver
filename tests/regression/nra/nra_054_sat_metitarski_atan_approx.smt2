; Meti-tarski atan(x) approximation: atan(x) ≈ x - x^3/3 + x^5/5 for small x.
; Truncation: |x - x^3/3 - atan_val| < eps with x in [-0.1, 0.1]. Sat with x=0.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const atan_val Real)
(assert (>= x (- (/ 1 10))))
(assert (<= x (/ 1 10)))
(assert (= atan_val (- x (/ (* x (* x x)) 3))))
(assert (>= atan_val (- (/ 1 5))))
(check-sat)
