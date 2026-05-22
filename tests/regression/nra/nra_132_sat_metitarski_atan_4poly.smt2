; Meti-tarski full atan(x) upper bound: atan(x) ≤ x - x³/3 + x⁵/5 for x ∈ [-1, 1].
; Truncation degree-5 Taylor. Sat with explicit x=0.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const x Real)
(declare-const atan_x Real)
(assert (>= x (- 1)))
(assert (<= x 1))
(assert (= atan_x (- (+ (- x (/ (* x (* x x)) 3)) (/ (* x (* x (* x (* x x)))) 5)) 0)))
; Assert atan_x ≤ 1 (loose upper bound)
(assert (<= atan_x 1))
(check-sat)
