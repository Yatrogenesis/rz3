; SPDX-License-Identifier: MIT
; Signed zero of an exactly-zero floating-point result (IEEE 754-2019 6.3); Z3 5.1.0: sat
(set-logic QF_FP)(assert (= (fp.mul RNE ((_ to_fp 8 24) RNE (- 1.0)) (_ +zero 8 24)) (_ -zero 8 24)))(check-sat)
