; Constant propagation must retain bindings extracted below a negated implication.
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-const x Int)
(declare-fun f (Int) Int)
(assert (not (=> (and (= x 4) (= (f x) 7) (distinct (f 4) 7)) false)))
(check-sat)
