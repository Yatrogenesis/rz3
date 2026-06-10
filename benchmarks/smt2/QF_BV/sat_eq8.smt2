(set-logic QF_BV)
(declare-fun b () (_ BitVec 8))
(assert (= b #b00000101))
(check-sat)
