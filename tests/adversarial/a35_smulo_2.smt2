(set-logic QF_BV)
(declare-const x (_ BitVec 2))(declare-const y (_ BitVec 2))
(assert (bvsmulo x y))
(check-sat)(get-model)
