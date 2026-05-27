; Nonlinear div/mod on pure Int (soft_float class). (mod x 2) is in {0,1}, so its
; square is in {0,1}; requiring it to equal 2 is unsatisfiable. Locks the
; false-SAT direction for incomplete nonlinear mod reasoning: a solver verdict
; of `sat` here is the OPPOSITE of the oracle and is flagged UNSOUND, and a
; `unknown` regression (losing the proof) is an UNEXPECTED_FAIL. The frontend
; div/mod lowering plus the NIA modular reasoning must keep this unsat.
(set-logic QF_NIA)
(set-info :status unsat)
(declare-const x Int)
(assert (= (* (mod x 2) (mod x 2)) 2))
(check-sat)
