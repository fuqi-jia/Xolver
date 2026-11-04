; A true residual formula must export a model, including declared symbols.
(set-option :produce-models true)
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-const x Int)
(declare-fun unused (Int) Int)
(assert (and true (= x x)))
(check-sat)
(get-model)
