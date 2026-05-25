; Scaled IDL parity: 2x-2y=3 has no integer solution (2*(x-y) is even, 3 is odd).
; Must be unsat (rhs/mag = 3/2 is non-integer => ImmediateConflict in the Eq case).
(set-logic QF_IDL)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (= (- (* 2 x) (* 2 y)) 3))
(check-sat)
