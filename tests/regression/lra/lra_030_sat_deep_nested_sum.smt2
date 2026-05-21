; Deep nested + : ((((a+b)+c)+d)+e) = 5.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const a Real) (declare-const b Real) (declare-const c Real)
(declare-const d Real) (declare-const e Real)
(assert (= (+ (+ (+ (+ a b) c) d) e) 5))
(assert (= a 1)) (assert (= b 1)) (assert (= c 1)) (assert (= d 1))
(check-sat)
