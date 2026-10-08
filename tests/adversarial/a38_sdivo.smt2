(set-logic QF_BV)
(declare-const x (_ BitVec 64))(declare-const y (_ BitVec 64))
(assert (bvsdivo x y))
(check-sat)(get-model)
