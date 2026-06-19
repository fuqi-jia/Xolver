; #75 regression: two stores of the SAME base at DISTINCT constant indices,
; asserted equal via a, force both writes to be no-ops (v=c[0], w=c[2]), so a=c.
; Then g(c)=g(a) by congruence, contradicting (distinct (g c) (g a)). UNSAT by
; array extensionality. The disequality is INDIRECT (g over arrays), so the
; direct-extensionality lemma never fires between a and c; the store-store no-op
; merge (XOLVER_AX_STORE_NOOP, default-ON) closes it. Previously a false sat.
(set-logic QF_AUFLRA)
(set-info :status unsat)
(declare-fun a () (Array Real Real))
(declare-fun c () (Array Real Real))
(declare-fun v () Real)
(declare-fun w () Real)
(declare-fun g ((Array Real Real)) Real)
(assert (= a (store c 0.0 v)))
(assert (= a (store c 2.0 w)))
(assert (distinct (g c) (g a)))
(check-sat)
