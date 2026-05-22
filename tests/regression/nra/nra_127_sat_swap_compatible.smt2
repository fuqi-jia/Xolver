; Inspired by typical SMT-COMP NRA: tight polynomial system requiring CDCAC.
; Constraints share variables forming a dependency graph.
(set-logic QF_NRA)
(set-info :status sat)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (> a 0))
(assert (> b 0))
(assert (> c 0))
(assert (> d 0))
(assert (= (* a b) (* c d)))
(assert (= (+ a b) (+ c d)))
(assert (distinct (+ a c) (+ b d)))
; Witness: (a,b,c,d)=(1,2,1,2). ab=2, cd=2 ✓; a+b=3, c+d=3 ✓; a+c=2, b+d=4, distinct ✓.
(check-sat)
