; Collatz-like step: n_next = ite(n mod 2 = 0, n/2, 3n+1). With n=5: 16; with n=16: 8.
; SAT: explicit n=5, n_next = 16.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const n Int)
(declare-const n_next Int)
(assert (= n 5))
(assert (= n_next (ite (= (mod n 2) 0) (div n 2) (+ (* 3 n) 1))))
(assert (= n_next 16))
(check-sat)
