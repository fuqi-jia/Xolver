; Div/mod by zero: the solver may choose any total extension, so sat.
; Exercises Part-2 partial-function model output (define-fun div/mod shadows).
(set-logic QF_UFNIA)
(set-info :status sat)
(set-option :produce-models true)
(declare-const a Int)
(assert (= (div a 0) 5))
(assert (= (mod a 0) 7))
(check-sat)
