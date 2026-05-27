(set-logic QF_NIA)
(set-info :status unsat)
; Locks fix 851f46e: a div/mod (mod by powers of two) formula that is UNSAT but
; whose linear-mod lowering admits a spurious model -> previously returned a
; WRONG `sat` (the validate-sat floor only fired for hasNonlinear, and mod-by-
; constant is linear). The default path now floors it to `unknown` (sound), so
; this is a KNOWN_FAIL (unknown vs unsat). If the false-SAT regresses, the solver
; returns `sat` = the OPPOSITE of the oracle = UNSOUND (caught, never lenient).
; (Structure mirrors an SV-COMP soft-float encoding; identifiers anonymized.)
(declare-fun n () Int)
(declare-fun m () Int)
(assert (let ((_c (not (= n 1))))
  (and (or (< (mod m 4294967296) 16777216) _c)
       (or (< (mod m 16777216) 65536) _c))))
(assert (not (let ((_c (not (= n 1))))
  (and (or _c (< (mod m 268435456) 1048576))
       (or (< (mod m 4294967296) 16777216) _c)
       (or (< (mod m 67108864) 262144) _c)
       (or (< (mod m 33554432) 131072) _c)
       (or (< (mod m 1073741824) 4194304) _c)
       (or (< (mod m 2147483648) 8388608) _c)
       (or (< (mod m 134217728) 524288) _c)
       (or (< (mod m 536870912) 2097152) _c)))))
(check-sat)
(exit)
