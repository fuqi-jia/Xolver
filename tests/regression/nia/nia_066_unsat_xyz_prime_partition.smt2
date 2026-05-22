; x*y*z = 6 with x,y,z prime — 6 = 2*3*1 but 1 not prime. UNSAT.
; To force "prime": each in {2,3,5,7}. Then xyz=6 requires factor 1 — impossible.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (or (= x 2) (= x 3) (= x 5) (= x 7)))
(assert (or (= y 2) (= y 3) (= y 5) (= y 7)))
(assert (or (= z 2) (= z 3) (= z 5) (= z 7)))
(assert (= (* x (* y z)) 6))
(check-sat)
