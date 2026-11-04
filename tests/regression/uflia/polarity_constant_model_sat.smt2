; A model must satisfy the required binding as well as its UF application.
(set-option :produce-models true)
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-const x Int)
(declare-fun f (Int) Int)
(assert (not (=> (and (= x 4) (= (f x) 7)) false)))
(check-sat)
(get-model)
