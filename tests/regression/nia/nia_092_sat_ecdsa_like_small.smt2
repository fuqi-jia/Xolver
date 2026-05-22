; Tiny ECC-like equation: y² = x³ + 1 (mod prime). Use Z (not mod) for tractability.
; (x,y) with y² = x³ + 1 — sat at (0,1), (-1, 0), (2, 3).
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (>= x (- 5))) (assert (<= x 5))
(assert (>= y 0)) (assert (<= y 10))
(assert (= (* y y) (+ (* x (* x x)) 1)))
(check-sat)
