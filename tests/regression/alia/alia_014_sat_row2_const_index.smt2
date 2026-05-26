(set-logic QF_ALIA)
(set-info :status sat)
; Read-over-write with distinct constant indices is consistent: the write at
; index 1 does not affect the read at index 2 (Row2), and Row1 pins index 1.
(declare-const a (Array Int Int))
(assert (= (select (store a 1 10) 1) 10))
(assert (= (select (store a 1 10) 2) (select a 2)))
(check-sat)
