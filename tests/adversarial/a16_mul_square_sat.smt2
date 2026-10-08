(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)
(assert (= (* x y) 36))(assert (> x y))(assert (> y 1))(assert (< x 18))
(check-sat)(get-model)
