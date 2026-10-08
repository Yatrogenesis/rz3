(set-logic QF_NIA)
(declare-const x Int)
(assert (= (mod x x) 5))
(check-sat)(get-model)
