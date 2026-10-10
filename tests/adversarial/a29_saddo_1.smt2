(set-logic QF_BV)
(declare-const x (_ BitVec 1))(declare-const y (_ BitVec 1))
(assert (bvsaddo x y))
(check-sat)(get-model)
