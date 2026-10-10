; SPDX-License-Identifier: MIT
(set-info :smt-lib-version 2.6)
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const i Int)
(declare-fun f (Int) Int)
(assert (and (= (f i) i) (distinct (select (store A (f i) 7) i) 7)))
(check-sat)
(exit)
