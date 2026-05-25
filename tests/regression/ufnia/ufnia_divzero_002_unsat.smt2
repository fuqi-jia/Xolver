; a = b forces (div a 0) = (div b 0) by congruence (div-by-zero is a function),
; contradicting 5 != 6. Guards the partial-function consistency requirement.
(set-logic QF_UFNIA)
(set-info :status unsat)
(declare-const a Int)
(declare-const b Int)
(assert (= (div a 0) 5))
(assert (= (div b 0) 6))
(assert (= a b))
(check-sat)
