; Dark-shadow + splinter target (Omega §2.3): the thin slab 2x <= 3y <= 2x+1 is
; real-feasible, but pinned at x=2 the window for 3y is [4,5], which contains no
; multiple of 3. The dark shadow fails and both splinters (3y=4, 3y=5) are empty,
; so the splinter recursion proves UNSAT. z3-confirmed.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(assert (>= (- (* 3 y) (* 2 x)) 0))
(assert (<= (- (* 3 y) (* 2 x)) 1))
(assert (= x 2))
(check-sat)
