(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(assert (bvnego x))
(check-sat)(get-model)
