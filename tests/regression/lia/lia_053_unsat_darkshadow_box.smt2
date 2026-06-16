; Dark-shadow target (Omega §2.3): the REAL relaxation is feasible (x=0.5, y=1
; gives 2x+3y=4), but no integer point in the unit box satisfies 2x+3y=4 —
; {0,1}^2 yields {0,2,3,5}, never 4. Catching this needs the integer-specific
; dark shadow, not just the real Fourier-Motzkin shadow. z3-confirmed unsat.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (>= (+ (* 2 x) (* 3 y)) 4))
(assert (<= (+ (* 2 x) (* 3 y)) 4))
(assert (>= x 0)) (assert (<= x 1))
(assert (>= y 0)) (assert (<= y 1))
(check-sat)
