(set-logic QF_FP)
(assert (fp.isNaN (fp #b0 #b11111111 #b00000000000000000000001)))
(check-sat)
