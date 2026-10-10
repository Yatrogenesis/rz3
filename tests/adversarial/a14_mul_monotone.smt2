(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)(declare-const z Int)
(assert (> x 2))(assert (> y 3))(assert (< (* x y) 12))
(check-sat)
