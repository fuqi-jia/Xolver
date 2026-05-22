; 5-variable diophantine: a+b+c+d+e = 20, a*b*c*d*e ≥ 100, each in [1,10].
; Sat e.g. (2,2,2,2,12)? 12 out of range. Try (1,2,3,4,10): sum=20, product=240. SAT.
(set-logic QF_NIA)
(set-info :status sat)
(declare-const a Int) (declare-const b Int) (declare-const c Int)
(declare-const d Int) (declare-const e Int)
(assert (>= a 1)) (assert (<= a 10))
(assert (>= b 1)) (assert (<= b 10))
(assert (>= c 1)) (assert (<= c 10))
(assert (>= d 1)) (assert (<= d 10))
(assert (>= e 1)) (assert (<= e 10))
(assert (= (+ a b c d e) 20))
(assert (>= (* a (* b (* c (* d e)))) 100))
(check-sat)
