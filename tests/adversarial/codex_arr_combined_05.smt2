; SPDX-License-Identifier: MIT
; SMT-LIB 2.6 differential QA
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-fun f (Int) Int)
(assert (and (= (f i) j) (= B (store A (f i) 7)) (distinct (select B j) 7)))
(check-sat)
(exit)
