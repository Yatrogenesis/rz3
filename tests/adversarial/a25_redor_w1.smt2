(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(assert (distinct (bvredor x) x))
(check-sat)
