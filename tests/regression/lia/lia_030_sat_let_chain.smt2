; Chained let bindings.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (let ((a x))
         (let ((b (+ a 1)))
           (let ((c (+ b 1)))
             (= c 5)))))
(check-sat)
