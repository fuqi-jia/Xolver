(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (* skoZ (* skoZ (/ 1 6)))) (+ (+ (/ 1 10) (* skoX (* skoX (* skoX (/ (- 1) 6))))) (* skoY (* skoY (* skoY (/ (- 1) 6))))))) (and (not (<= skoZ (/ 1 10))) (and (not (<= skoY (/ 1 10))) (and (not (<= skoX (/ 1 10))) (and (not (<= (/ 11 10) skoZ)) (and (not (<= (/ 11 10) skoY)) (not (<= (/ 11 10) skoX)))))))))
(check-sat)
(exit)
