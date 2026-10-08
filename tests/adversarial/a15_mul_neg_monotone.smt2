(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)
(assert (< x (- 2)))(assert (> y 3))(assert (> (* x y) (- 6)))
(check-sat)
