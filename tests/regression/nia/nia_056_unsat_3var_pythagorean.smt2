; Three-square sum = 7 has no solution in non-negative ints (Legendre: 7 = 4(8k+7) form).
; Actually 7 is reachable: 4+1+1+1, but only 3 squares. Check.
; 7 = 4+1+1+1 (4 squares); 3-square = ? Allowed only if not 4^a(8b+7) — 7 IS 8·0+7, not allowed.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (>= x 0)) (assert (<= x 4))
(assert (>= y 0)) (assert (<= y 4))
(assert (>= z 0)) (assert (<= z 4))
(assert (= (+ (* x x) (* y y) (* z z)) 7))
(check-sat)
